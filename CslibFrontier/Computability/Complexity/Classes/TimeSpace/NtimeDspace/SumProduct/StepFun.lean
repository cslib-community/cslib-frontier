/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.ListTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.Space

/-!
# The step of the evaluator on codes

`stepF` is the evaluator's step acting on codes of states, written with the
decoding functions `hdF`, `tlF`, `consF`. It is the function the program term of
`SumProduct.StepTerm` computes. The oracles are numeric functions of the path
code: `qt`, `qp`, `qa` give the tag, the precision and the parameter of a node,
and `qb k` a leaf bit (nonzero meaning `1`).

`stepF_code`: on the code of a state whose stack and path have matching shapes,
`stepF` computes the code of the next state.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open NatList

section

variable (qt qp qa : ℕ → ℕ) (qb : ℕ → ℕ → ℕ)

/-- The code of a four-entry list. -/
def mkF (a b c d : ℕ) : ℕ := consF a (consF b (consF c (consF d 1)))

/-- Push a frame onto a code of frames. -/
def pushF (k j l c F : ℕ) : ℕ := consF k (consF j (consF l (consF c F)))

/-- After a split of a product node. -/
def advF (k j l c Fr ρ : ℕ) : ℕ :=
  if l < j then mkF 1 (l + 1) (pushF k j (l + 1) c Fr) (consF 0 ρ)
  else if j < k then mkF 1 0 (pushF k (j + 1) 0 (c / 2) Fr) (consF 0 ρ)
  else mkF 0 (c % 2) Fr ρ

/-- A call. -/
def callF (v F Pa : ℕ) : ℕ :=
  if v < qp Pa then
    if qt Pa < 1 then mkF 0 (if 0 < qb v Pa then 1 else 0) F Pa
    else if qt Pa < 3 then mkF 1 0 (pushF v 0 0 0 F) (consF 0 Pa)
    else if qt Pa < 4 then mkF 1 (v + qa Pa) (pushF v 0 0 0 F) (consF 0 Pa)
    else mkF 0 0 F Pa
  else mkF 0 0 F Pa

/-- A return to a sum node. -/
def sumRetF (v k j l c Fr i ρ par : ℕ) : ℕ :=
  if i + 1 < 2 ^ par then mkF 1 j (pushF k j l (c + v) Fr) (consF (i + 1) ρ)
  else if j < k then mkF 1 (j + 1) (pushF k (j + 1) l ((c + v) / 2) Fr) (consF 0 ρ)
  else mkF 0 ((c + v) % 2) Fr ρ

/-- A return to a product node. -/
def prodRetF (v k j l c Fr i ρ : ℕ) : ℕ :=
  if 0 < i then advF k j l (c + v) Fr ρ
  else if 0 < v then mkF 1 (j - l) (pushF k j l c Fr) (consF 1 ρ)
  else advF k j l c Fr ρ

/-- A return. -/
def retF (v F Pa : ℕ) : ℕ :=
  if F < 2 then mkF 0 v F Pa
  else
    let k := hdF F
    let F1 := tlF F
    let j := hdF F1
    let F2 := tlF F1
    let l := hdF F2
    let F3 := tlF F2
    let c := hdF F3
    let Fr := tlF F3
    let i := hdF Pa
    let ρ := tlF Pa
    if qt ρ < 1 then mkF 0 v Fr ρ
    else if qt ρ < 2 then sumRetF v k j l c Fr i ρ (qa ρ)
    else if qt ρ < 3 then prodRetF v k j l c Fr i ρ
    else mkF 0 v Fr ρ

/-- One step on codes. -/
def stepF (S : ℕ) : ℕ :=
  let m := hdF S
  let r1 := tlF S
  let v := hdF r1
  let r2 := tlF r1
  let F := hdF r2
  let r3 := tlF r2
  let Pa := hdF r3
  if 0 < m then callF qt qp qa qb v F Pa else retF qt qa v F Pa

/-- The oracles of the abstract machine, read off numeric oracles. -/
def numQ (π : List ℕ) : Info := ⟨qt (enc π), qp (enc π), qa (enc π)⟩

/-- The leaf oracle of the abstract machine. -/
def numLB (π : List ℕ) (k : ℕ) : Bool := decide (0 < qb k (enc π))

end

theorem mkF_eq (a b c d : ℕ) : mkF a b c d = enc [a, b, c, d] := by
  simp [mkF, ← enc_nil]

theorem pushF_eq (f : Frame) (fr : List Frame) :
    pushF f.k f.j f.l f.c (enc (flatFrames fr)) = enc (flatFrames (f :: fr)) := by
  simp [pushF, flatFrames, Frame.toList]

theorem code_eq (st : State) :
    st.code = mkF st.call.toNat st.v (enc (flatFrames st.frames)) (enc st.path) := by
  rw [mkF_eq]; rfl

theorem enc_flat_lt_two_iff (fr : List Frame) : enc (flatFrames fr) < 2 ↔ fr = [] := by
  cases fr with
  | nil => simp [flatFrames]
  | cons f fr =>
    simp only [flatFrames, List.flatMap_cons, Frame.toList, List.cons_append, reduceCtorEq,
      iff_false, not_lt]
    exact two_le_enc_cons _ _

variable {qt qp qa : ℕ → ℕ} {qb : ℕ → ℕ → ℕ}

theorem flatFrames_cons (f : Frame) (fr : List Frame) :
    flatFrames (f :: fr) = f.k :: f.j :: f.l :: f.c :: flatFrames fr := rfl

theorem pushF_eq' (k j l c : ℕ) (fr : List Frame) :
    pushF k j l c (enc (flatFrames fr)) = enc (flatFrames (⟨k, j, l, c⟩ :: fr)) := by
  simp [pushF, flatFrames_cons]

theorem advF_eq (k j l c : ℕ) (fr : List Frame) (ρ : List ℕ) :
    advF k j l c (enc (flatFrames fr)) (enc ρ) = (advanceProd k j l c fr ρ).code := by
  unfold advF advanceProd
  split_ifs <;> simp only [code_eq, Bool.toNat_true, Bool.toNat_false, pushF_eq', consF_enc]

/-- **The step on codes is the step of the machine.** -/
theorem stepF_code (st : State) (hshape : st.frames ≠ [] → st.path ≠ []) :
    stepF qt qp qa qb st.code = (step (numQ qt qp qa) (numLB qb) st).code := by
  obtain ⟨call, v, fr, π⟩ := st
  conv_lhs => rw [State.code]
  simp only [stepF, hdF_enc_cons, tlF_enc_cons]
  cases call with
  | true =>
    simp only [Bool.toNat_true, zero_lt_one, ite_true, callF, step, numQ, numLB]
    by_cases hP : v < qp (enc π)
    · have hP' : ¬ qp (enc π) ≤ v := by omega
      simp only [hP, hP', ite_true, ite_false]
      by_cases h0 : qt (enc π) < 1
      · have e : qt (enc π) = 0 := by omega
        simp only [e, ite_true, code_eq, Bool.toNat_false]
        by_cases hb : 0 < qb v (enc π) <;> simp [hb]
      · have e0 : qt (enc π) ≠ 0 := by omega
        by_cases h3 : qt (enc π) < 3
        · have e : qt (enc π) = 1 ∨ qt (enc π) = 2 := by omega
          simp only [h0, e0, h3, e, ite_true, ite_false, code_eq, Bool.toNat_true, pushF_eq',
            consF_enc]
        · have e : ¬ (qt (enc π) = 1 ∨ qt (enc π) = 2) := by omega
          by_cases h4 : qt (enc π) < 4
          · have e3 : qt (enc π) = 3 := by omega
            simp [e3, code_eq, pushF_eq', consF_enc]
          · have e3 : qt (enc π) ≠ 3 := by omega
            simp only [h0, e0, h3, e, h4, e3, ite_false, code_eq, Bool.toNat_false]
    · have hP' : qp (enc π) ≤ v := by omega
      simp only [hP, hP', ite_true, ite_false, code_eq, Bool.toNat_false]
  | false =>
    simp only [Bool.toNat_false, lt_irrefl, ite_false, retF]
    cases fr with
    | nil =>
      simp only [enc_flat_lt_two_iff, ite_true, step, code_eq, Bool.toNat_false]
    | cons f fr =>
      cases π with
      | nil => exact absurd rfl (hshape (by simp))
      | cons i ρ =>
        obtain ⟨k, j, l, c⟩ := f
        have hF : ¬ enc (k :: j :: l :: c :: flatFrames fr) < 2 := by
          have := two_le_enc_cons k (j :: l :: c :: flatFrames fr); omega
        simp only [flatFrames_cons, hF, ite_false, hdF_enc_cons, tlF_enc_cons, step, numQ,
          List.tail_cons, List.headD_cons]
        by_cases h0 : qt (enc ρ) < 1
        · have : qt (enc ρ) ≠ 1 ∧ qt (enc ρ) ≠ 2 := by omega
          simp [h0, this.1, this.2, code_eq]
        · by_cases h1 : qt (enc ρ) < 2
          · have e : qt (enc ρ) = 1 := by omega
            simp only [ite_true, e]
            unfold sumRetF
            by_cases ha : i + 1 < 2 ^ qa (enc ρ)
            · simp [ha, code_eq, pushF_eq', consF_enc]
            · by_cases hb : j < k
              · simp [ha, hb, code_eq, pushF_eq', consF_enc]
              · simp [ha, hb, code_eq]
          · by_cases h2 : qt (enc ρ) < 3
            · have e : qt (enc ρ) = 2 := by omega
              simp only [ite_true, e]
              unfold prodRetF
              by_cases hi : 0 < i
              · simp [hi, show i ≠ 0 by omega, advF_eq]
              · have hi0 : i = 0 := by omega
                subst hi0
                by_cases hv : 0 < v
                · simp [hv, show v ≠ 0 by omega, code_eq, pushF_eq', consF_enc]
                · have hv0 : v = 0 := by omega
                  subst hv0
                  simp [advF_eq]
            · have : qt (enc ρ) ≠ 1 ∧ qt (enc ρ) ≠ 2 := by omega
              simp [h0, h1, h2, this.1, this.2, code_eq]

end Cslib.Complexity.NtimeDspace.SumProduct
