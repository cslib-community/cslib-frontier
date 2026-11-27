/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Sort.Runs
import CslibFrontier.Foundations.Data.List.KeyedFlatMap

/-!
# Words on several channels, prefix codes, and choices of letters

Provides `Tape.on` (broadcasting one word across a set of channels), unique decodability of
prefix-free `flatMap` codes (`Tape.flatMap_inj`), and `Tape.Runs.letter` / `Tape.Runs.word`
building blocks.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Sort.Words`.

## Main definitions

* `Tape.on`: assign the word `w` to every channel in `zs` and `[]` outside.

## Main results

* `Tape.flatMap_inj`: injectivity of `List.flatMap` for prefix-free non-empty codes.
* `Tape.flatten_ofFn_single`, `Tape.flatten_ofFn_nil`.
* `Tape.Runs.letter`, `Tape.Runs.word`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Finset Cslib.Automata.Weighted

section Codes

variable {κ Γ : Type*}

theorem flatMap_inj {f : κ → List Γ} (hne : ∀ a, f a ≠ [])
    (hf : ∀ a b u v, f a ++ u = f b ++ v → a = b) :
    Function.Injective fun l : List κ => l.flatMap f := by
  intro l
  induction l with
  | nil =>
    rintro (_ | ⟨b, l'⟩) h
    · rfl
    · exact absurd (List.append_eq_nil_iff.1 h.symm).1 (hne b)
  | cons a l ih =>
    rintro (_ | ⟨b, l'⟩) h
    · exact absurd (List.append_eq_nil_iff.1 h).1 (hne a)
    · simp only [List.flatMap_cons] at h
      obtain rfl := hf a b _ _ h
      rw [ih (List.append_cancel_left h)]

theorem flatten_ofFn_single {k : ℕ} (i : Fin k) (w : Fin k → List Γ)
    (h : ∀ j, j ≠ i → w j = []) : (List.ofFn w).flatten = w i := by
  have hw (j : Fin k) : w j = if j = i then w j else [] := by
    by_cases e : j = i <;> simp [e, h j]
  rw [List.ofFn_eq_map, ← List.flatMap_def, List.flatMap_congr fun j _ => hw j]
  exact List.flatMap_ite_key_eq _ id w (by simpa using List.nodup_finRange k) (List.mem_finRange i)

theorem flatten_ofFn_nil {k : ℕ} (w : Fin k → List Γ) (h : ∀ j, w j = []) :
    (List.ofFn w).flatten = [] := by
  rw [List.flatten_eq_nil_iff]
  intro l hl
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
  exact h j

end Codes

section On

variable {Z Γ : Type*} [DecidableEq Z]

/-- Broadcast the word `w` onto every channel in `zs` (and `[]` elsewhere). -/
@[expose] def on (zs : Finset Z) (w : List Γ) : Z → List Γ :=
  fun z => if z ∈ zs then w else []

theorem on_append (zs : Finset Z) (w w' : List Γ) (z : Z) :
    on zs w z ++ on zs w' z = on zs (w ++ w') z := by
  unfold on
  split_ifs <;> simp

theorem flatMap_on {κ : Type*} (zs : Finset Z) (f : κ → List Γ) (l : List κ) (z : Z) :
    (l.flatMap fun k => on zs (f k) z) = on zs (l.flatMap f) z := by
  unfold on
  split_ifs <;> simp

theorem sum_on [Fintype Z] (zs : Finset Z) (w : List Γ) :
    ∑ z, (on zs w z).length = zs.card * w.length := by
  unfold on
  simp only [apply_ite List.length, List.length_nil]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]

end On

namespace Runs

variable {F Z Γ : Type*} [CommRing F] [Fintype Z] [DecidableEq Z] [Finite Γ]

/-- Choose a letter `k : κ` and write `f k` on every channel of `zs`, with weight `c k`. -/
theorem letter {κ : Type*} [Fintype κ] (zs : Finset Z) (f : κ → Γ) (c : κ → F) :
    Runs (Fintype.card κ * (2 * zs.card + 1)) (fun k => on zs [f k]) c :=
  (pick (fun k => on zs [f k]) c).mono (by simp [sum_on])

/-- Write a fixed word `w` on every channel of `zs`, with weight `1`. -/
theorem word (zs : Finset Z) (w : List Γ) :
    Runs (2 * (zs.card * w.length) + 1) (fun _ : Unit => on zs w) (fun _ => (1 : F)) :=
  (const (on zs w)).mono (by rw [sum_on])

end Runs

end Cslib.Circuits.Arithmetic.Separation.Tape
