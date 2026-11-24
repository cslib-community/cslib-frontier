/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.SingleTape.TM0Restrict
public import Mathlib.Computability.Halting
public import Mathlib.Computability.TuringMachine.Config
public import Mathlib.Computability.TuringMachine.ToPartrec
public import CslibFrontier.Computability.Machines.Turing.TM2.PartrecToTM2
import Mathlib.Logic.Relation

/-!
# Universal finite-state `TM0` machine

This module constructs a fixed universal Post–Turing machine `M₀'` in Mathlib's `Turing.TM0` model,
with a finite state type and finite tape alphabet.

Starting from a `ToPartrec` code `univ` that evaluates the `n`-th partial recursive code on input
`0` (`ToPartrec.Code.exists_code`), Mathlib's compilers `PartrecToTM2`, `TM2to1` and `TM1to0` turn
`univ` into a fixed `TM0` machine `M₀`. Applying state-set restriction (`TM0.restrict`) along its
finite support produces `M₀'`.

The input tape for a natural number `n` is `input n`, computed primitive recursively
(`primrec_input`). The machine halts on `input n` if and only if the `n`-th partial recursive code
halts on `0` (`eval_dom_iff`).

## Main definitions

* `Turing.TM0.Universal.univ`: fixed `ToPartrec` code evaluating the `n`-th code at `0`.
* `Turing.TM0.Universal.M₀`: compiled `TM0` machine simulating `univ`.
* `Turing.TM0.Universal.M₀'`: restriction of `M₀` to its finite reachable state set.
* `Turing.TM0.Universal.input`: input tape encoding a natural number `n`.

## Main results

* `Turing.TM0.Universal.dom_M₀'`: `(M₀'.eval (input n)).Dom ↔ (univ.eval [n]).Dom`.
* `Turing.TM0.Universal.eval_dom_iff`: `(M₀'.eval (input n)).Dom` iff the `n`-th code halts on `0`.
* `Turing.TM0.Universal.primrec_input`: the input encoding `input` is primitive recursive.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Turing.TM0.Universal

open Relation Turing StateTransition ToPartrec PartrecToTM2

theorem exists_univ : ∃ u : Code, ∀ n : ℕ,
    (u.eval [n]).Dom ↔ ((Denumerable.ofNat Nat.Partrec.Code n).eval 0).Dom := by
  have hf : Partrec fun n : ℕ => (Denumerable.ofNat Nat.Partrec.Code n).eval 0 :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)
  obtain ⟨u, hu⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  refine ⟨u, fun n => ?_⟩
  have h : u.eval [n] = pure <$> (Denumerable.ofNat Nat.Partrec.Code n).eval 0 := hu ⟨[n], rfl⟩
  rw [h]
  rfl

/-- A `ToPartrec` code evaluating, on input `[n]`, the `n`-th partial recursive function at
`0`. -/
noncomputable def univ : Code := Classical.choose exists_univ

theorem univ_spec (n : ℕ) :
    (univ.eval [n]).Dom ↔ ((Denumerable.ofNat Nat.Partrec.Code n).eval 0).Dom :=
  Classical.choose_spec exists_univ n

/-- The labels of the `TM2` machine compiled from `univ`, with initial label the compiled
program. -/
@[expose] def UΛ : Type := Λ'

noncomputable instance : Inhabited UΛ := ⟨trNormal univ Cont'.halt⟩

/-- The `TM2` machine compiled from `univ`. -/
def M₂ : UΛ → TM2.Stmt (fun _ : K' => Γ') UΛ (Option Γ') := tr

/-- The `TM1` machine simulating `M₂`. -/
noncomputable def M₁ := TM2to1.tr M₂

/-- The `TM0` machine simulating `M₁`. -/
noncomputable def M₀ := TM1to0.tr M₁

theorem supports₂ : TM2.Supports M₂ (codeSupp univ Cont'.halt : Finset UΛ) :=
  tr_supports univ Cont'.halt

/-- The finite set of `TM1` labels used by `M₁`. -/
noncomputable def S₁ := TM2to1.trSupp M₂ (codeSupp univ Cont'.halt : Finset UΛ)

theorem supports₁ : TM1.Supports M₁ S₁ := TM2to1.tr_supports M₂ supports₂

/-- The finite set of `TM0` states used by `M₀`. -/
noncomputable def S₀ := TM1to0.trStmts M₁ S₁

theorem supports₀ : TM0.Supports M₀ (S₀ : Set (TM1to0.Λ' M₁)) := TM1to0.tr_supports M₁ supports₁

noncomputable instance : Inhabited (S₀ : Set (TM1to0.Λ' M₁)) := ⟨⟨default, supports₀.1⟩⟩

/-- The restriction of `M₀` to its finitely many reachable states. -/
noncomputable def M₀' : TM0.Machine (TM2to1.Γ' K' fun _ => Γ') (S₀ : Set (TM1to0.Λ' M₁)) :=
  TM0.restrict M₀ supports₀

private theorem tm2_init_eq (v : List ℕ) :
    (TM2.init K'.main (trList v) : TM2.Cfg (fun _ : K' => Γ') UΛ (Option Γ')) =
      PartrecToTM2.init univ v := by
  simp only [TM2.init, PartrecToTM2.init]
  congr 1 with k : 1
  cases k <;> rfl

private theorem dom_M₂ (n : ℕ) :
    (TM2.eval M₂ K'.main (trList [n])).Dom ↔ (univ.eval [n]).Dom := by
  rw [TM2.eval, Part.map_Dom, tm2_init_eq]
  have := tr_eval univ [n]
  change StateTransition.eval (TM2.step M₂) _ = _ at this
  rw [this]
  rfl

/-- The tape alphabet of `M₀` is primcodable through an enumeration. -/
noncomputable instance primcodableTapeΓ : Primcodable (TM2to1.Γ' K' fun _ : K' => Γ') :=
  letI := Classical.decEq (TM2to1.Γ' K' fun _ : K' => Γ')
  Primcodable.ofEquiv _ (Fintype.equivFin _)

/-- The state set of `M₀'` is primcodable through an enumeration. -/
noncomputable instance primcodableS₀ : Primcodable (S₀ : Set (TM1to0.Λ' M₁)) :=
  letI := Classical.decEq (S₀ : Set (TM1to0.Λ' M₁))
  Primcodable.ofEquiv _ (Fintype.equivFin _)

private theorem primrec_trInit :
    Primrec (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main) := by
  let G := TM2to1.Γ' K' fun _ : K' => Γ'
  let f : Γ' → G := fun a => (false, Function.update (fun _ => none) K'.main (some a))
  let g : G → G := fun x => (true, x.2)
  have hf : Primrec f := Primrec.dom_finite _
  have hL : Primrec fun L : List Γ' => L.reverse.map f :=
    Primrec.list_map Primrec.list_reverse (hf.comp Primrec.snd).to₂
  have hg : Primrec g := Primrec.dom_finite _
  exact (Primrec.list_cons.comp (hg.comp (Primrec.list_headI.comp hL))
    (Primrec.list_tail.comp hL)).of_eq fun _ => rfl

/-- The input tape of `M₀'` holding the number `n`. -/
noncomputable def input (n : ℕ) : List (TM2to1.Γ' K' fun _ : K' => Γ') :=
  TM2to1.trInit K'.main (trList [n])

/-- The encoding of input numbers as tape configurations for `M₀'` is primitive recursive. -/
theorem primrec_input : Primrec input := by
  have : Primrec fun n : ℕ => trList [n] :=
    (Primrec.list_append.comp primrec_trNat (Primrec.const [Γ'.cons])).of_eq fun _ => rfl
  exact (primrec_trInit.comp this).of_eq fun _ => rfl

/-- `M₀'` halts on `input n` if and only if `univ` halts on `[n]`. -/
theorem dom_M₀' (n : ℕ) :
    (TM0.eval M₀' (input n)).Dom ↔ (univ.eval [n]).Dom := by
  rw [input, M₀', TM0.eval_restrict_dom M₀ supports₀, M₀, TM1to0.tr_eval, M₁,
    TM2to1.tr_eval_dom, dom_M₂]

/-- `M₀'` halts on `input n` if and only if the `n`-th partial recursive code halts on `0`. -/
theorem eval_dom_iff (n : ℕ) :
    (TM0.eval M₀' (input n)).Dom ↔ ((Denumerable.ofNat Nat.Partrec.Code n).eval 0).Dom := by
  rw [dom_M₀', univ_spec]

end Turing.TM0.Universal
