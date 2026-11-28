/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Sort.RunVal
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Sort.Words
public import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.EquivFin

/-!
# Letters and tapes of the universal program

Defines the alphabet `Uni.Sy M K`, tape names `Uni.Tp K`, channel type `Uni.Zc K`, record letter
injections (`Uni.be`, `Uni.ol`), and the star-over-letters combinator `Tape.Runs.wordstar`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.Alpha`.

## Main definitions

* `Uni.Sy`: tape alphabet (bits, semicolons, modes, record kinds, columns, marks, dots, flags,
  block separators).
* `Uni.Bl`: record key letters `K ⊕ (Fin 4 → Bool)`.
* `Uni.be`, `Uni.ol`: embeddings into `Sy M K`.
* `Uni.Tp`, `Uni.Zc`: tape names and channels of the universal program.

## Main results

* `Tape.Runs.wordstar`: write an arbitrary word over `κ` onto every channel in `zs`.
* `Uni.ol_inj`, `Uni.ol_ne_dot`, `Uni.ol_ne_bar`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Cslib.Automata.Weighted

/-- Write an arbitrary word over `κ` on every channel of `zs`, using dimension
`card κ * (2 * zs.card + 1) + 1`. -/
theorem Runs.wordstar {F Z Γ κ : Type*} [CommRing F] [Fintype Z] [DecidableEq Z] [Finite Γ]
    [Fintype κ] (zs : Finset Z) (hz : zs.Nonempty) (f : κ → Γ) :
    Runs (Fintype.card κ * (2 * zs.card + 1) + 1)
      (fun l : List κ => on zs (l.map f)) (fun _ => (1 : F)) := by
  obtain ⟨z₀, hz₀⟩ := hz
  have h := (Runs.letter (F := F) zs f fun _ => 1).kstar fun k => ⟨z₀, by simp [on, hz₀]⟩
  refine h.congr (Equiv.refl _) (fun l z => ?_) fun l => by simp
  rw [Equiv.refl_apply, flatMap_on]
  congr 1
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih, List.map_cons]; rfl

end Cslib.Circuits.Arithmetic.Separation.Tape

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Cslib.Circuits.Arithmetic.Separation.Tape

/-- Letters of the universal tape program: bits, word separator, modes, record kinds, 4-bit
columns, rotation mark, record end dot, lookup flag, and block separator bar. -/
inductive Sy (M K : Type) where
  /-- a binary digit -/
  | bit (x : Bool)
  /-- end of a binary word -/
  | semi
  /-- pointer-machine mode -/
  | md (m : M)
  /-- record kind -/
  | kd (k : K)
  /-- a 4-bit column slice of a record -/
  | col (c : Fin 4 → Bool)
  /-- rotation mark inside a record -/
  | mark
  /-- end of a record -/
  | dot
  /-- flag (`false`: table entry, `true`: lookup) -/
  | flag (f : Bool)
  /-- end of a pass/block -/
  | bar
  deriving DecidableEq, Fintype

instance instFiniteSy {M K : Type} [Finite M] [Finite K] : Finite (Sy M K) := by
  classical
  let _ : Fintype M := Fintype.ofFinite M
  let _ : Fintype K := Fintype.ofFinite K
  infer_instance

/-- Alphabet of record key letters (`K` or 4-bit column). -/
abbrev Bl (K : Type) := K ⊕ (Fin 4 → Bool)

variable {M K : Type}

/-- Embed a record letter into `Sy M K`. -/
@[expose] def be : Bl K → Sy M K
  | .inl k => .kd k
  | .inr c => .col c

/-- Embed a record letter or the rotation mark (`none`) into `Sy M K`. -/
@[expose] def ol : Option (Bl K) → Sy M K
  | none => .mark
  | some b => be b

theorem ol_inj : Function.Injective (ol : Option (Bl K) → Sy M K) := by
  rintro (_ | (a | a)) (_ | (b | b)) h <;> simp [ol, be] at h <;> simp [h]

theorem ol_ne_dot (o : Option (Bl K)) : (ol o : Sy M K) ≠ .dot := by
  rcases o with _ | (a | a) <;> simp [ol, be]

theorem ol_ne_bar (o : Option (Bl K)) : (ol o : Sy M K) ≠ .bar := by
  rcases o with _ | (a | a) <;> simp [ol, be]

/-- Tape names of the universal program: five registers, mode, counter pair, fresh addresses,
lookups, sorted list, radix buckets, and comparison copies. -/
inductive Tp (K : Type) where
  /-- register tape `i` -/
  | rg (i : Fin 5)
  /-- mode tape -/
  | md
  /-- counter tape -/
  | cp
  /-- fresh address tape -/
  | fr
  /-- lookup tape -/
  | lk
  /-- main list tape -/
  | ls
  /-- radix bucket tape for letter `b` -/
  | bk (b : Bl K)
  /-- comparison copy tape `k` -/
  | cm (k : Bool)
  deriving DecidableEq, Fintype

/-- Channels of the universal program (tape sides plus one input channel `Unit`). -/
abbrev Zc (K : Type) := Ch (Tp K) Unit

end Cslib.Circuits.Arithmetic.Separation.Uni
