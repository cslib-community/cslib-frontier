/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.CmpU

/-!
# The sorting loop: channel emissions and block structure

Block-separator unique-parsing lemmas (`Uni.cut_inj`, `Uni.blocks`, `Uni.blocks_inj`), record
list encodings (`Uni.encW`), and the exact channel-by-channel emission equations for the full
radix-sorting loop (`Uni.XU`, `Uni.emU`, `Uni.runs_U`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.SpecU`.

## Main definitions

* `Uni.blocks`: concatenate words each terminated by a separator symbol `a`.
* `Uni.encW`, `Uni.dIn`, `Uni.dOut`, `Uni.fIn`, `Uni.fOut`, `Uni.cOut`.
* `Uni.XU`, `Uni.emU`, `Uni.dimU`: combined sorting-and-comparison run type and dimension bound.

## Main results

* `Uni.cut_inj`, `Uni.blocks_inj`, `Uni.length_blocks`.
* `Uni.rw'_inj`, `Uni.encW_inj`, `Uni.runs_U`.
* `Uni.emU_lsT`, `Uni.emU_lsF`, `Uni.emU_bk_false`, `Uni.emU_bk_true`, `Uni.emU_cm_false`,
  `Uni.emU_cm_true`, `Uni.emU_other`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset Cslib.Automata.Weighted Cslib.Circuits.Arithmetic.Separation.Tape

section Blocks

variable {Γ : Type*}

/-- Two words separated by the first occurrence of `a` split uniquely. -/
theorem cut_inj {a : Γ} {w w' x x' : List Γ} (hw : a ∉ w) (hw' : a ∉ w')
    (h : w ++ a :: x = w' ++ a :: x') : w = w' ∧ x = x' := by
  induction w generalizing w' with
  | nil =>
    rcases w' with _ | ⟨b, w'⟩
    · simpa using h
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by simp [h.1]) hw'
  | cons b w ih =>
    rcases w' with _ | ⟨b', w'⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by simp [h.1]) hw
    · simp only [List.cons_append, List.cons.injEq, List.mem_cons, not_or] at h hw hw'
      obtain ⟨h1, h2⟩ := ih hw.2 hw'.2 h.2
      exact ⟨by rw [h.1, h1], h2⟩

/-- Concatenate words `ws`, appending separator `a` after each block. -/
@[expose] def blocks (a : Γ) (ws : List (List Γ)) : List Γ :=
  ws.flatMap fun w => w ++ [a]

theorem blocks_cons (a : Γ) (w : List Γ) (ws : List (List Γ)) :
    blocks a (w :: ws) = w ++ a :: blocks a ws := by
  simp [blocks]

theorem blocks_append (a : Γ) (ws ws' : List (List Γ)) :
    blocks a (ws ++ ws') = blocks a ws ++ blocks a ws' := by
  simp [blocks]

theorem blocks_inj {a : Γ} {ws ws' : List (List Γ)} (h : ∀ w ∈ ws, a ∉ w)
    (h' : ∀ w ∈ ws', a ∉ w) (e : blocks a ws = blocks a ws') : ws = ws' := by
  induction ws generalizing ws' with
  | nil => rcases ws' with _ | ⟨w', ws'⟩ <;> simp [blocks] at e ⊢
  | cons w ws ih =>
    rcases ws' with _ | ⟨w', ws'⟩
    · simp [blocks] at e
    · rw [blocks_cons, blocks_cons] at e
      obtain ⟨h1, h2⟩ := cut_inj (h w (by simp)) (h' w' (by simp)) e
      rw [h1, ih (fun w hw => h w (by simp [hw])) (fun w hw => h' w (by simp [hw])) h2]

theorem length_blocks (a : Γ) (ws : List (List Γ)) :
    (blocks a ws).length = (ws.map List.length).sum + ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [blocks_cons, List.length_append, List.length_cons, ih, List.map_cons,
      List.sum_cons, List.length_cons]
    omega

end Blocks

section Enc

variable {M K : Type}

theorem rw'_inj {f f' : Bool} {w w' : List (Option (Bl K))} {u v : List (Sy M K)}
    (h : rw' f w ++ u = rw' f' w' ++ v) : f = f' ∧ w = w' ∧ u = v := by
  simp only [rw', List.cons_append, List.cons.injEq, Sy.flag.injEq, List.append_assoc] at h
  obtain ⟨rfl, h⟩ := h
  have hd (w : List (Option (Bl K))) : (Sy.dot : Sy M K) ∉ w.map ol := fun hw =>
    let ⟨o, _, ho⟩ := List.mem_map.1 hw; ol_ne_dot o ho
  obtain ⟨h1, h2⟩ := cut_inj (hd w) (hd w') h
  exact ⟨rfl, List.map_injective_iff.2 ol_inj h1, h2⟩

/-- Concatenated tape encoding of a list of records (with rotation marks). -/
@[expose] def encW (l : List (Bool × List (Option (Bl K)))) : List (Sy M K) :=
  l.flatMap fun r => rw' r.1 r.2

theorem encW_inj :
    Function.Injective (encW : List (Bool × List (Option (Bl K))) → List (Sy M K)) := by
  refine flatMap_inj (fun _ => by simp [rw']) fun ⟨f, w⟩ ⟨f', w'⟩ u v h => ?_
  obtain ⟨rfl, rfl, -⟩ := rw'_inj h
  rfl

theorem bar_rw' (f : Bool) (w : List (Option (Bl K))) : (Sy.bar : Sy M K) ∉ rw' f w := by
  simp [rw', fun o => ol_ne_bar (M := M) o]

theorem bar_encW (l : List (Bool × List (Option (Bl K)))) :
    (Sy.bar : Sy M K) ∉ encW l := by
  rw [encW, List.mem_flatMap]
  exact fun ⟨r, _, h⟩ => bar_rw' _ _ h

/-- The records consumed from `lsT` by a distribution pass `d`. -/
@[expose] def dIn (d : List (Dr K)) : List (Bool × List (Option (Bl K))) :=
  d.map fun r => (r.flag, some r.head :: r.tail)

/-- The records written to bucket `b` by a distribution pass `d`. -/
@[expose] def dOut [DecidableEq K] (b : Bl K) (d : List (Dr K)) :
    List (Bool × List (Option (Bl K))) :=
  (d.filter fun r => r.head = b).map fun r => (r.flag, r.tail ++ [some r.head])

/-- The records consumed by the final mark-dropping pass. -/
@[expose] def fIn (l : List (Rk K)) : List (Bool × List (Option (Bl K))) :=
  l.map fun r => (r.1, none :: r.2.map some)

/-- The records emitted by the final mark-dropping pass. -/
@[expose] def fOut (l : List (Rk K)) : List (Bool × List (Option (Bl K))) :=
  l.map fun r => (r.1, r.2.map some)

end Enc

/-- Concatenated output written to `lsF` by bucket collection `m`. -/
@[expose] noncomputable def cOut {M K : Type} [Fintype K]
    (m : Bl K → List (NB M K)) : List (Sy M K) :=
  ((bsl K).flatMap m).map Subtype.val

/-- Complete run of the universal radix-sorting and neighbour-comparison phase. -/
@[ext]
structure XU (M K : Type) where
  /-- sequence of radix-sort passes -/
  passes : List (Ps M K)
  /-- final list of records read when the rotation marks return to the front -/
  final : List (Rk K)
  /-- neighbour comparison run on the two copies of the sorted list -/
  cmp : XG (List (Bl K))

variable {M K : Type} [Fintype K] [DecidableEq K]

/-- Emissions of a complete sort-and-compare run `x : XU M K`. -/
@[expose] noncomputable def emU (x : XU M K) : Zc K → List (Sy M K) := fun z =>
  (x.passes.flatMap fun p => emPs p z) ++ (emFi x.final z ++ emCm x.cmp z)

/-- Dimension upper bound for the full sort-and-compare automaton. -/
@[expose] def dimU (m k : ℕ) : ℕ :=
  (dimPs m k + 1) + ((14 + 3 + (k * 7 + 1) + 7 + 1 + 3) + dimCm k)

theorem runs_U {A : Type*} [CommRing A] [Fintype M] :
    Runs (dimU (Fintype.card (Sy M K)) (Fintype.card (Bl K)))
      (emU : XU M K → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  classical
  have hne (p : Ps M K) : ∃ z, emPs p z ≠ [] :=
    ⟨lsT, fun heq => by simpa [emPs, on, barSet] using congrArg List.length heq⟩
  exact (((runs_ps (A := A) (M := M) (K := K)).kstar hne).mul
    ((runs_fi (A := A) (M := M) (K := K)).mul (runs_cm (A := A) (M := M) (K := K)))).congr
    ⟨fun x => (x.passes, x.final, x.cmp), fun y => ⟨y.1, y.2.1, y.2.2⟩,
     fun _ => rfl, fun _ => rfl⟩
    (fun _ _ => rfl) fun _ => by simp

section Values

private theorem mem_barSet_lsT : (lsT : Zc K) ∈ barSet := by simp [barSet]

private theorem mem_barSet_bk (b : Bl K) : (.tp (.bk b) false : Zc K) ∈ barSet := by simp [barSet]

private theorem not_barSet {z : Zc K} (h1 : z ≠ lsT) (h2 : ∀ b, z ≠ .tp (.bk b) false) :
    z ∉ barSet := by
  simp only [barSet, mem_insert, mem_image, mem_univ, true_and, not_or, not_exists]
  exact ⟨h1, fun b e => h2 b e.symm⟩

theorem emCo_lsF (m : Bl K → List (NB M K)) : emCo m lsF = cOut m ++ [Sy.bar] := by
  unfold emCo cOut
  have h1 (i : Fin (Fintype.card (Bl K))) :
      on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
          ((m ((Fintype.equivFin (Bl K)).symm i)).map Subtype.val) (lsF : Zc K) ++
        on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [(Sy.bar : Sy M K)] lsF =
        (m ((Fintype.equivFin (Bl K)).symm i)).map Subtype.val := by simp [on]
  simp only [h1]
  rw [bsl, List.map_flatMap, List.flatMap_def, List.map_ofFn]
  simp only [on, mem_singleton, ↓reduceIte]; rfl

theorem emCo_bk_true (m : Bl K → List (NB M K)) (b : Bl K) :
    emCo m (.tp (.bk b) true) = (m b).map Subtype.val ++ [Sy.bar] := by
  unfold emCo
  rw [flatten_ofFn_single (Fintype.equivFin (Bl K) b)]
  · simp [on]
  · intro k hk
    simp [on, show b ≠ (Fintype.equivFin (Bl K)).symm k by rintro rfl; simp at hk]

theorem emCo_other (m : Bl K → List (NB M K)) {z : Zc K} (h1 : z ≠ lsF)
    (h2 : ∀ b, z ≠ .tp (.bk b) true) : emCo m z = [] := by
  unfold emCo
  rw [flatten_ofFn_nil]
  · simp [on, h1]
  · intro _
    simp [on, h1, h2]

theorem emPs_lsT (p : Ps M K) : emPs p lsT = encW (dIn p.1) ++ [Sy.bar] := by
  have h2 (d : Dr K) : (emDr d lsT : List (Sy M K)) = rw' d.flag (some d.head :: d.tail) := by
    simp [emDr, on]
  unfold emPs
  rw [emCo_other _ (by simp) (by simp)]
  simp only [h2, on, mem_barSet_lsT, ↓reduceIte, List.append_nil, encW, dIn, List.flatMap_map]

theorem emPs_lsF (p : Ps M K) : emPs p lsF = cOut p.2 ++ [Sy.bar] := by
  have h2 (d : Dr K) : (emDr d lsF : List (Sy M K)) = [] := by simp [emDr, on]
  unfold emPs
  rw [emCo_lsF]
  simp [h2, on, not_barSet (z := lsF) (by simp) (by simp)]

theorem emPs_bk_false (p : Ps M K) (b : Bl K) :
    emPs p (.tp (.bk b) false) = encW (dOut b p.1) ++ [Sy.bar] := by
  have h2 (d : Dr K) : (emDr d (.tp (.bk b) false) : List (Sy M K)) =
      if d.head = b then rw' d.flag (d.tail ++ [some d.head]) else [] := by
    by_cases h : d.head = b <;> simp [emDr, on, h, Ne.symm]
  have h3 (l : List (Dr K)) : (l.flatMap fun d =>
      (if d.head = b then rw' d.flag (d.tail ++ [some d.head]) else [] : List (Sy M K))) =
      (l.filter fun d => d.head = b).flatMap fun d => rw' d.flag (d.tail ++ [some d.head]) := by
    induction l with
    | nil => rfl
    | cons d l ih =>
      rw [List.flatMap_cons, ih, List.filter_cons]; by_cases h : d.head = b <;> simp [h]
  unfold emPs
  rw [emCo_other _ (by simp) (by simp)]
  simp only [h2, on, mem_barSet_bk, ↓reduceIte, List.append_nil, h3, encW, dOut, List.flatMap_map]

theorem emPs_bk_true (p : Ps M K) (b : Bl K) :
    emPs p (.tp (.bk b) true) = (p.2 b).map Subtype.val ++ [Sy.bar] := by
  have h2 (d : Dr K) : (emDr d (.tp (.bk b) true) : List (Sy M K)) = [] := by simp [emDr, on]
  unfold emPs
  rw [emCo_bk_true]
  simp [h2, on, not_barSet (z := .tp (.bk b) true) (by simp) (by simp)]

theorem emPs_other (p : Ps M K) {z : Zc K} (h1 : z ≠ lsT) (h2 : z ≠ lsF)
    (h3 : ∀ b s, z ≠ .tp (.bk b) s) : emPs p z = [] := by
  have e2 (d : Dr K) : (emDr d z : List (Sy M K)) = [] := by simp [emDr, on, h1, h3]
  unfold emPs
  rw [emCo_other _ h2 fun b => h3 b true]
  simp [e2, on, not_barSet h1 fun b => h3 b false]

omit [Fintype K] in
theorem emFi_lsT (l : List (Rk K)) :
    (emFi l lsT : List (Sy M K)) = encW (fIn l) ++ [Sy.bar] := by
  simp [emFi, on, encW, fIn, List.flatMap_map]

omit [Fintype K] in
theorem emFi_cm (l : List (Rk K)) (k : Bool) :
    (emFi l (.tp (.cm k) false) : List (Sy M K)) = encW (fOut l) := by
  cases k <;> simp [emFi, on, encW, fOut, List.flatMap_map]

omit [Fintype K] in
theorem emFi_other (l : List (Rk K)) {z : Zc K} (h1 : z ≠ lsT)
    (h2 : ∀ k, z ≠ .tp (.cm k) false) : (emFi l z : List (Sy M K)) = [] := by
  simp [emFi, on, h1, h2]

omit [Fintype K] [DecidableEq K] in
private theorem rk_flatMap (l : List (Rk K)) : (l.flatMap rk : List (Sy M K)) = encW (fOut l) := by
  rw [encW, fOut, List.flatMap_map]; rfl

omit [Fintype K] in
theorem emCm_true (y : XG (List (Bl K))) (k : Bool) :
    (emCm y (.tp (.cm k) true) : List (Sy M K)) =
      encW (fOut (if k then QlG y else PlG y)) := by
  cases k <;> simp [emCm, on, ← rk_flatMap]

omit [Fintype K] in
theorem emCm_other (y : XG (List (Bl K))) {z : Zc K} (h : ∀ k, z ≠ .tp (.cm k) true) :
    (emCm y z : List (Sy M K)) = [] := by
  simp [emCm, on, h]

theorem emU_lsT (x : XU M K) :
    emU x lsT = blocks Sy.bar (x.passes.map (fun p => encW (dIn p.1)) ++ [encW (fIn x.final)]) := by
  unfold emU
  rw [emFi_lsT, emCm_other _ (by simp), blocks_append]
  simp [emPs_lsT, blocks, List.flatMap_map]

theorem emU_lsF (x : XU M K) :
    emU x lsF = blocks Sy.bar (x.passes.map fun p => cOut p.2) := by
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_other _ (by simp)]
  simp [emPs_lsF, blocks, List.flatMap_map]

theorem emU_bk_false (x : XU M K) (b : Bl K) :
    emU x (.tp (.bk b) false) =
      blocks Sy.bar (x.passes.map fun p => encW (dOut b p.1)) := by
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_other _ (by simp)]
  simp [emPs_bk_false, blocks, List.flatMap_map]

theorem emU_bk_true (x : XU M K) (b : Bl K) :
    emU x (.tp (.bk b) true) =
      blocks Sy.bar (x.passes.map fun p => (p.2 b).map Subtype.val) := by
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_other _ (by simp)]
  simp [emPs_bk_true, blocks, List.flatMap_map]

theorem emU_cm_false (x : XU M K) (k : Bool) :
    emU x (.tp (.cm k) false) = encW (fOut x.final) := by
  unfold emU
  rw [emFi_cm, emCm_other _ (by simp)]
  simp [fun p : Ps M K => emPs_other p (z := .tp (.cm k) false) (by simp) (by simp) (by simp)]

theorem emU_cm_true (x : XU M K) (k : Bool) :
    emU x (.tp (.cm k) true) =
      encW (fOut (if k then QlG x.cmp else PlG x.cmp)) := by
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_true]
  simp [fun p : Ps M K => emPs_other p (z := .tp (.cm k) true) (by simp) (by simp) (by simp)]

theorem emU_other (x : XU M K) {z : Zc K} (h1 : z ≠ lsT) (h2 : z ≠ lsF)
    (h3 : ∀ b s, z ≠ .tp (.bk b) s) (h4 : ∀ k s, z ≠ .tp (.cm k) s) :
    emU x z = [] := by
  unfold emU
  rw [emFi_other _ h1 (fun k => h4 k false), emCm_other _ (fun k => h4 k true)]
  simp [fun p : Ps M K => emPs_other p h1 h2 h3]

end Values

end Cslib.Circuits.Arithmetic.Separation.Uni
