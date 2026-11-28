/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunWord

/-!
# Certificates of matched runs

A run of an automaton on tapes and inputs is certified by its states, the positions of the heads,
and the contents of the tapes (`Tape.Good`). The certificate of a run is unique, and it exists if
and only if the run is matched (`Tape.Good.matched`, `Tape.exists_good`).

For the matrix-product path expansion originally named `prod_ofFn_apply` in `Nc.RunGood`, reuse
`Matrix.list_prod_ofFn_apply` from `CslibFrontier.Foundations.LinearAlgebra.Matrix.ListProd`
(together with `List.map_ofFn`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.RunGood`.

## Main definitions

* `Tape.Ch.start`: channels whose head positions start at `0`.
* `Tape.Good`: local consistency conditions on a matched-run certificate.
* `Tape.place0`: initial position of each channel in a run.

## Main results

* `Tape.Good.place`, `Tape.Good.place_last`, `Tape.Good.place_zero`, `Tape.Good.contents`:
  uniqueness of the certificate positions and tape contents for a given run `o`.
* `Tape.Good.matched`: every valid certificate witnesses a matched run.
* `Tape.exists_good`: every matched run admits a valid certificate when `N + t < M`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

/-- The channels whose head positions start at `0` (all tape sides, and input `0`). -/
@[expose] def Ch.start {S : Type*} {n : ℕ} : Ch S (Fin n) → Bool
  | .tp _ _ => true
  | .inp j => j.1 = 0

/-- Local certificate conditions for a matched run: emitted letters `o`, states `q`, head
positions `P`, tape contents `c`, and one-hot input code `x`. -/
structure Good {Γ S Q : Type*} [DecidableEq S] {n t M N : ℕ}
    (i e : Q) (x : Fin N × Option Γ → Bool)
    (o : Fin t → Letter S (Fin n) Γ) (q : Fin (t + 1) → Q)
    (P : Ch S (Fin n) → Fin (t + 1) → Fin M) (c : S → Fin M → Option Γ) : Prop where
  /-- The run begins at state `i`. -/
  first : q 0 = i
  /-- The run ends at state `e`. -/
  last : q (Fin.last t) = e
  /-- Starting channels begin at position `0`. -/
  zero : ∀ z, z.start = true → (P z 0).1 = 0
  /-- At step `τ`, channel `z`'s head advances if and only if `o τ` emits on `z`. -/
  step : ∀ z τ, (P z (Fin.succ τ)).1 = (P z (Fin.castSucc τ)).1 + (emit [o τ] z).length
  /-- Consecutive input channels are linked by `1` for the separator marker. -/
  link : ∀ j j' : Fin n, j'.1 = j.1 + 1 →
    (P (.inp j') 0).1 = (P (.inp j) (Fin.last t)).1 + 1
  /-- Each write/read on tape `s` agrees with `c s`. -/
  write : ∀ s b τ γ, o τ = some (.tp s b, γ) →
    c s (P (.tp s b) (Fin.castSucc τ)) = some γ
  /-- Tape cells beyond the final head position of side `(s, b)` are blank (`none`). -/
  blank : ∀ s b p, P (.tp s b) (Fin.last t) ≤ p → c s p = none
  /-- Each input emission agrees with the one-hot code `x`. -/
  read : ∀ j τ γ, o τ = some (.inp j, γ) →
    ∃ h : (P (.inp j) (Fin.castSucc τ)).1 < N, x (⟨_, h⟩, some γ) = true
  /-- At the end of input `j`, `x` holds the `none` separator. -/
  sep : ∀ j, ∃ h : (P (.inp j) (Fin.last t)).1 < N, x (⟨_, h⟩, none) = true

section Forward

variable {Γ S Q : Type*} [DecidableEq S] {n t M N : ℕ}
variable {i e : Q} {u : Fin n → List Γ} {o : Fin t → Letter S (Fin n) Γ} {q : Fin (t + 1) → Q}
  {P : Ch S (Fin n) → Fin (t + 1) → Fin M} {c : S → Fin M → Option Γ}

theorem emit_take_succ (o : Fin t → Letter S (Fin n) Γ) (z : Ch S (Fin n)) (τ : Fin t) :
    (emit ((List.ofFn o).take (τ + 1)) z).length =
      (emit ((List.ofFn o).take τ) z).length + (emit [o τ] z).length := by
  simp [List.take_add_one, emit_appendR]

/-- The starting position of each channel in a run `o`. -/
@[expose] def place0 (o : Fin t → Letter S (Fin n) Γ) : Ch S (Fin n) → ℕ
  | .tp _ _ => 0
  | .inp j => base (fun j => emit (List.ofFn o) (.inp j)) j

theorem Good.place {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c)
    (z : Ch S (Fin n)) (τ : Fin (t + 1)) :
    (P z τ).1 = (P z 0).1 + (emit ((List.ofFn o).take τ) z).length := by
  induction τ using Fin.induction with
  | zero => simp
  | succ τ ih =>
    rw [h.step, ih, Fin.val_succ, emit_take_succ, Fin.val_castSucc]
    omega

theorem Good.place_last {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c)
    (z : Ch S (Fin n)) :
    (P z (Fin.last t)).1 = (P z 0).1 + (emit (List.ofFn o) z).length := by
  rw [h.place, Fin.val_last, List.take_of_length_le (by simp)]

theorem Good.place_zero {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c)
    (z : Ch S (Fin n)) :
    (P z 0).1 = place0 o z := by
  rcases z with ⟨s, b⟩ | ⟨m, hm⟩
  · exact h.zero _ rfl
  · induction m with
    | zero => simp [h.zero (.inp ⟨0, hm⟩) rfl, place0]
    | succ m ih =>
      have hm' : m < n := Nat.lt_of_succ_lt hm
      rw [h.link ⟨m, hm'⟩ ⟨m + 1, hm⟩ rfl, h.place_last, ih hm']
      simpa [place0] using (base_succ (fun j => emit (List.ofFn o) (.inp j)) ⟨m, hm'⟩).symm

theorem Good.contents {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c)
    (s : S) (b : Bool) (p : Fin M) :
    c s p = (emit (List.ofFn o) (.tp s b))[p.1]? := by
  by_cases hp : p.1 < (emit (List.ofFn o) (.tp s b)).length
  · obtain ⟨τ, γ, h1, h2, h3⟩ := exists_emit _ _ _ hp
    rw [List.length_ofFn] at h1
    have hP : P (.tp s b) (Fin.castSucc ⟨τ, h1⟩) = p :=
      Fin.ext (by rw [h.place, h.zero _ rfl, Fin.val_castSucc, zero_add, h3])
    rw [← hP, h.write s b ⟨τ, h1⟩ γ (by simpa [List.getElem?_ofFn, h1] using h2), hP,
      ← h3, emit_getElem _ _ _ _ h2]
  · rw [List.getElem?_eq_none (by omega), h.blank s b p]
    rw [Fin.le_def, h.place_last, h.zero _ rfl]
    omega

theorem Good.matched [DecidableEq Γ] (hM : t < M) (h : Good i e (code N u) o q P c) :
    Matched (List.ofFn o) u := by
  refine ⟨fun s => List.ext_getElem? fun p => ?_, fun j =>
    (congrFun (eq_of_read u (fun j => emit (List.ofFn o) (.inp j)) fun k p hp => ?_) j).symm⟩
  · by_cases hp : p < M
    · rw [← h.contents s false ⟨p, hp⟩, ← h.contents s true ⟨p, hp⟩]
    · have h1 := emit_length_le (List.ofFn o) (.tp s false)
      have h2 := emit_length_le (List.ofFn o) (.tp s true)
      simp only [List.length_ofFn] at h1 h2
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · rcases hp.lt_or_eq with hp | rfl
    · obtain ⟨τ, γ, h1, h2, h3⟩ := exists_emit _ _ _ hp
      rw [List.length_ofFn] at h1
      obtain ⟨_, hx⟩ := h.read k ⟨τ, h1⟩ γ (by simpa [List.getElem?_ofFn, h1] using h2)
      have hx' := of_decide_eq_true hx
      rw [h.place, h.place_zero, Fin.val_castSucc, h3] at hx'
      simp only [place0] at hx'
      rw [hx', List.getElem?_append_left (by simpa using hp), List.getElem?_map,
        ← h3, emit_getElem _ _ _ _ h2]
      rfl
    · obtain ⟨_, hx⟩ := h.sep k
      have hx' := of_decide_eq_true hx
      rw [h.place_last, h.place_zero] at hx'
      simpa [place0] using hx'

end Forward

section Backward

variable {Γ S Q : Type*} [DecidableEq S] {n t M N : ℕ}
variable {i e : Q} {u : Fin n → List Γ} {o : Fin t → Letter S (Fin n) Γ} {q : Fin (t + 1) → Q}

private theorem emit_take_le (o : Fin t → Letter S (Fin n) Γ) (z : Ch S (Fin n)) (τ : ℕ) :
    (emit ((List.ofFn o).take τ) z).length ≤ (emit (List.ofFn o) z).length := by
  conv_rhs => rw [← List.take_append_drop τ (List.ofFn o), emit_appendR, List.length_append]
  omega

private theorem place_lt (hM : N + t < M) (hN : (wordOf (List.ofFn u)).length ≤ N)
    (hu : ∀ j, emit (List.ofFn o) (.inp j) = u j) (z : Ch S (Fin n)) (τ : ℕ) :
    place0 o z + (emit ((List.ofFn o).take τ) z).length < M := by
  have h1 := emit_take_le o z τ
  rcases z with ⟨s, b⟩ | j
  · have h2 := emit_length_le (List.ofFn o) (.tp s b)
    simp only [place0, List.length_ofFn] at h2 ⊢
    omega
  · have h2 := base_add_lt u j
    simp only [place0, funext hu]
    rw [hu] at h1
    omega

theorem exists_good [DecidableEq Γ] (hM : N + t < M) (hN : (wordOf (List.ofFn u)).length ≤ N)
    (h : Matched (List.ofFn o) u) (hi : q 0 = i) (he : q (Fin.last t) = e) :
    ∃ (P : Ch S (Fin n) → Fin (t + 1) → Fin M) (c : S → Fin M → Option Γ),
      Good i e (code N u) o q P c := by
  have h3 : (fun j => emit (List.ofFn o) (.inp j)) = u := funext h.2
  refine ⟨fun z τ => ⟨_, place_lt hM hN h.2 z τ⟩,
    fun s p => (emit (List.ofFn o) (.tp s false))[p.1]?, hi, he,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (⟨s, b⟩ | j) hz <;> simp_all [Ch.start, place0]
  · intro z τ
    simp only [Fin.val_succ, Fin.val_castSucc, emit_take_succ]
    omega
  · intro j j' hj
    simp [place0, List.take_of_length_le, h.2, hj, base_succ]
  · intro s b τ γ ho
    have hg := emit_getElem (List.ofFn o) (.tp s b) τ γ (by simp [ho])
    cases b <;> simpa [place0, h.1 s] using hg
  · intro s b p hp
    rw [Fin.le_def] at hp
    simp only [place0, Fin.val_last, zero_add] at hp
    rw [List.take_of_length_le (by simp)] at hp
    cases b <;> exact List.getElem?_eq_none (by simpa [h.1 s] using hp)
  · intro j τ γ ho
    have hg := emit_getElem (List.ofFn o) (.inp j) τ γ (by simp [ho])
    rw [h.2] at hg
    have hlt := (List.getElem?_eq_some_iff.1 hg).1
    have hb := base_add_lt u j
    simp only [place0, h3, Fin.val_castSucc]
    refine ⟨by omega, decide_eq_true ?_⟩
    rw [wordOf_getElem, List.getElem?_append_left (by simpa using hlt), List.getElem?_map, hg]
    rfl
  · intro j
    have hb := base_add_lt u j
    have hP : place0 o (.inp j) + (emit ((List.ofFn o).take t) (.inp j)).length =
        base u j + (u j).length := by simp [place0, List.take_of_length_le, h.2]
    exact ⟨lt_of_eq_of_lt (by simpa using hP) (by omega),
      decide_eq_true (by simp [hP, wordOf_getElem])⟩

end Backward

end Cslib.Circuits.Arithmetic.Separation.Tape
