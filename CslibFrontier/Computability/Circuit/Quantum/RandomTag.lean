/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Uniform
import CslibFrontier.Computability.Circuit.Quantum.Reversible.Sampling
import CslibFrontier.Computability.Circuit.Quantum.Input
import CslibFrontier.Computability.Circuit.Quantum.Output
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.GetD

/-!
# Running a uniform quantum circuit on a random tagged input

A Hadamard gate generates a fair tag bit. The circuit copies the tag and input into a fresh block,
runs the given circuit there, and returns the tag on wire zero and the circuit decision on wire one.
Keeping the tag outside the block makes the two branches have disjoint measurement supports.
-/

public section

namespace Cslib.Quantum

open GateCode Reversible Turing.MultiTapeTM Finset

private def tagCopy (n : ℕ) := outputCopyCodes (n + 2) (n + 3) ((n + 2) :: List.range n)

private def tagReadout (n : ℕ) := swapWireCodes 1 (n + 3) ++ swapWireCodes 0 (n + 2)

private theorem copy_classical {n m : ℕ} (hm : n + 1 ≤ m) :
    IsClassical (n + 3 + m) (tagCopy n) :=
  isClassical_outputCopyCodes (by omega) (by simp; omega)

private theorem readout_classical {n m : ℕ} (hm : 0 < m) :
    IsClassical (n + 3 + m) (tagReadout n) :=
  IsClassical.append.mpr ⟨isClassical_swapWireCodes (by omega) (by omega) (by omega),
    isClassical_swapWireCodes (by omega) (by omega) (by omega)⟩

/-- On input `x`, generate a fair bit `b`, run `F` on `b :: x`, and output `b` on wire
zero and the decision of `F` on wire one. -/
def UniformCircuitFamily.randomTag (F : UniformCircuitFamily) : UniformCircuitFamily where
  width n := n + 3 + F.width (n + 1)
  gates n := [(true, n + 2, [])] ++ (tagCopy n ++
    ((F.gates (n + 1)).map (shift (n + 3)) ++ tagReadout n))
  computableInPolyTime_width := by have := F.computableInPolyTime_width; fun_prop
  computableInPolyTime_gates := by
    have := F.computableInPolyTime_gates
    have hc : ComputableInPolyTime tagCopy encUnary (encList encGateCode) := by
      unfold tagCopy outputCopyCodes outQubit
      fun_prop
    unfold tagReadout swapWireCodes shift
    fun_prop
  le_width n := by omega
  width_pos n := by omega
  wellFormed n g hg := by
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with rfl | hc | hg | hr
    · exact ⟨by omega, rfl⟩
    · exact (copy_classical (F.le_width _) _ hc).2
    · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
      exact (F.wellFormed _ _ hmem).shift le_rfl
    · exact (readout_classical (F.width_pos _) _ hr).2

private theorem read_copy_of_outside {n m i : ℕ} (hi : i < n + 3 ∨ n + 3 + (n + 1) ≤ i)
    (X : Fin m → Bool) : readBit (classicalRun (tagCopy n) X) i = readBit X i := by
  apply readBit_classicalRun_of_forall_ne
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  have := (List.mem_zipIdx hp).2.1
  simp only [List.length_cons, List.length_range] at this
  change n + 3 + p.2 ≠ i
  omega

private def tagBasis {n m : ℕ} (hm : n + 1 ≤ m) (x : List Bool) (b : Bool) :
    Fin (n + 3 + m) → Bool :=
  Function.update (inputState _ x) ⟨n + 2, by omega⟩ b

private theorem read_tagBasis {n m : ℕ} (hm : n + 1 ≤ m) (x : List Bool) (hx : x.length = n)
    (b : Bool) (i : ℕ) :
    readBit (tagBasis hm x b) i = if i = n + 2 then b else x.getD i false := by
  by_cases hi : i < n + 3 + m
  · rw [readBit_of_lt _ hi, tagBasis, Function.update_apply]
    simp [Fin.ext_iff, inputState]
  · rw [readBit_of_le _ (by omega), ite_eq_right (by omega), List.getD_eq_default _ _ (by omega)]

private theorem copied_tag {n m : ℕ} (hm : n + 1 ≤ m) (x : List Bool) (hx : x.length = n)
    (b : Bool) :
    classicalRun (tagCopy n) (tagBasis hm x b) ∘ blockEmb (n + 3) le_rfl =
      inputState m (b :: x) := by
  funext i
  have hi := i.isLt
  change classicalRun (tagCopy n) (tagBasis hm x b) (blockEmb (n + 3) le_rfl i) = _
  rw [← readBit_fin (classicalRun (tagCopy n) (tagBasis hm x b)) (blockEmb _ _ i),
    blockEmb_apply_val, Nat.add_comm i.val]
  change _ = (b :: x).getD i false
  by_cases h : i.val < n + 1
  · rw [tagCopy, readBit_classicalRun_outputCopyCodes (by omega) (by simp; omega) _
      (fun j _ => by rw [read_tagBasis hm x hx b, ite_eq_right (by omega)]
                     exact List.getD_eq_default _ _ (by omega)) (by simpa using h),
      read_tagBasis hm x hx b]
    cases heq : i.val with
    | zero => simp [outQubit]
    | succ j =>
      have hj : j < n := by omega
      simp [outQubit, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simpa using hj : j < (List.range n).length),
        min_eq_right (by omega : j ≤ n + 2),
        show j ≠ n + 2 by omega]
  · rw [read_copy_of_outside (Or.inr (by omega)), read_tagBasis hm x hx b, ite_eq_right (by omega),
      List.getD_eq_default x false (by omega), List.getD_eq_default _ _ (by simp; omega)]

private theorem sum_two_branches {m N : ℕ} (e : Fin m ↪ Fin N) (X : Bool → Fin N → Bool)
    (hX : ¬ AgreeOff e (X true) (X false)) (ψ : Bool → Qubits m)
    (P : (Fin N → Bool) → Prop) [DecidablePred P] :
    ∑ y, (if P y then ‖((embedState e (X true) (ψ true) +
      embedState e (X false) (ψ false)).ofLp y)‖ ^ 2 else 0) =
      ∑ b : Bool, ∑ z, if P (glue e z (X b)) then ‖(ψ b).ofLp z‖ ^ 2 else 0 := by
  classical
  have hy (y : Fin N → Bool) : ¬ (AgreeOff e y (X true) ∧ AgreeOff e y (X false)) :=
    fun h => hX (h.1.symm.trans h.2)
  have hs (b : Bool) := sum_agreeOff e (X b)
    (fun y => if P y then ‖(ψ b).ofLp (y ∘ e)‖ ^ 2 else 0)
  simp only [glue_comp] at hs
  rw [Fintype.sum_bool, ← hs true, ← hs false, ← sum_add_distrib]
  apply sum_congr rfl
  intro y _
  simp only [WithLp.ofLp_add, Pi.add_apply, embedState_apply]
  by_cases ht : AgreeOff e y (X true) <;> by_cases hf : AgreeOff e y (X false) <;>
    simp_all

private theorem tag_prob (F : UniformCircuitFamily) (x : List Bool) (joint : Bool) :
    F.randomTag.onesProb (if joint then [0, 1] else [1]) x =
      (∑ b : Bool, if joint → b then F.acceptProb (b :: x) else 0) / 2 := by
  classical
  let n := x.length
  let m := F.width (n + 1)
  have hm : n + 1 ≤ m := F.le_width _
  let N := n + 3 + m
  let e : Fin m ↪ Fin N := blockEmb (n + 3) le_rfl
  let X (b : Bool) := classicalRun (tagCopy n) (tagBasis hm x b)
  let ψ (b : Bool) := Circuit.run (Circuit.ofCodes m (F.gates (n + 1))) (inputState m (b :: x))
  let s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
  let S := if joint then [0, 1] else [1]
  have hl : n + 2 < N := by dsimp [N]; omega
  have ht (b : Bool) : readBit (X b) (n + 2) = b := by
    dsimp only [X]
    rw [read_copy_of_outside (Or.inl (by omega)), read_tagBasis hm x rfl, ite_eq_left rfl]
  have ho (i : Fin m) : (e i : ℕ) ≠ n + 2 := by
    change i.val + (n + 3) ≠ n + 2
    omega
  have hX : ¬ AgreeOff e (X true) (X false) := by
    intro h
    have he := h ⟨n + 2, hl⟩ fun i hij => ho i (congrArg Fin.val hij)
    rw [← readBit_of_lt (X true) hl, ← readBit_of_lt (X false) hl, ht, ht] at he
    contradiction
  have hbranch (b : Bool) :
      Circuit.eval (Circuit.ofCodes N ((F.gates (n + 1)).map (shift (n + 3)))) (ket (X b)) =
        embedState e (X b) (ψ b) := by
    have hb := copied_tag hm x rfl b
    have hi : X b = glue e (inputState m (b :: x)) (X b) := by
      rw [← hb]
      exact (glue_comp_of_agreeOff (.refl e (X b))).symm
    conv_lhs => rw [hi, ← embedState_ket]
    rw [Circuit.ofCodes_map_shift le_rfl (F.wellFormed _), Circuit.eval_mapWires_embedState]
    rfl
  have hH : Circuit.eval (Circuit.ofCodes N [(true, n + 2, [])]) (ket (inputState N x)) =
      s • (ket (tagBasis hm x true) + ket (tagBasis hm x false)) := by
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp
      (isSome_toPlacedGate?_iff.mpr (show WellFormed N (true, n + 2, []) from ⟨hl, rfl⟩))
    have hz : inputState N x ⟨n + 2, hl⟩ = false :=
      List.getD_eq_default _ _ (by dsimp [n]; omega)
    simp [Circuit.ofCodes, hg, eval_toPlacedGate_hadamard_ket hg hl, hz,
      tagBasis, smul_add, s, N]
  have hstate :
      Circuit.run (Circuit.ofCodes N (F.randomTag.gates n)) (inputState N x) =
        Circuit.eval (Circuit.ofCodes N (tagReadout n))
          (s • (embedState e (X true) (ψ true) + embedState e (X false) (ψ false))) := by
    change Circuit.eval (Circuit.ofCodes N (_ ++ (_ ++ (_ ++ _)))) _ = _
    have hc (b : Bool) : Circuit.eval (Circuit.ofCodes N (tagCopy n))
        (ket (tagBasis hm x b)) = ket (X b) := Circuit.eval_ofCodes_ket (copy_classical hm) _
    simp only [Circuit.ofCodes_append, Circuit.eval_append, hH, map_smul, map_add, hc, hbranch]
  have hs : ‖s‖ ^ 2 = 1 / 2 := by
    rw [show ‖s‖ = |(Real.sqrt 2)⁻¹| from (Complex.norm_real _).trans (Real.norm_eq_abs _)]
    rw [sq_abs, inv_pow, Real.sq_sqrt (by norm_num), one_div]
  have hread (b : Bool) (z : Fin m → Bool) :
      classicalRun (tagReadout n) (glue e z (X b)) ∈ onesAt N S ↔
        (joint → b) ∧ z ∈ accepting m := by
    let y := glue e z (X b)
    have h0 : readBit (classicalRun (tagReadout n) y) 0 = b := by
      rw [tagReadout, classicalRun_append, readBit_classicalRun_swapWireCodes (by omega)
        (by omega) hl, readBit_classicalRun_swapWireCodes_of_ne (by omega) (by omega),
        readBit_glue_of_forall_ne _ _ _ ho, ht]
    have h1 : readBit (classicalRun (tagReadout n) y) 1 = readBit z 0 := by
      have hh : n + 3 < N := by dsimp [N]; omega
      rw [tagReadout, classicalRun_append, readBit_classicalRun_swapWireCodes_of_ne
        (by omega) (by omega), readBit_classicalRun_swapWireCodes (by omega) (by omega) hh,
        readBit_of_lt _ hh, readBit_of_lt _ (by omega)]
      have hwire : (⟨n + 3, hh⟩ : Fin N) = e ⟨0, by omega⟩ := Fin.ext (by simp [e])
      rw [hwire]
      exact glue_apply_emb e z (X b) _
    change classicalRun (tagReadout n) y ∈ _ ↔ _
    cases joint <;> simp [S, accepting, mem_onesAt_iff, h0, h1, show 0 < m by omega,
      show 0 < N by omega, show 1 < N by omega]
  change measureProb (Circuit.run (Circuit.ofCodes N (F.randomTag.gates n)) (inputState N x))
    (onesAt N S) = _
  rw [hstate, map_smul, measureProb_smul, hs, Circuit.measureProb_eval_ofCodes
    (readout_classical (by omega : 0 < m)), sum_two_branches e X hX ψ, one_div, inv_mul_eq_div]
  congr 1
  refine sum_congr rfl fun b _ => ?_
  simp_rw [hread]
  by_cases hb : joint → b
  · simp only [iff_true_intro hb, true_and, ↓reduceIte]
    rw [← sum_filter]
    simp [UniformCircuitFamily.acceptProb, Quantum.acceptProb, measureProb, ψ, n, m]
  · simp [hb]

/-- The success probability when running the circuit on a fair random tag. -/
theorem UniformCircuitFamily.onesProb_randomTag (F : UniformCircuitFamily) (x : List Bool) :
    F.randomTag.onesProb [1] x = (F.acceptProb (true :: x) + F.acceptProb (false :: x)) / 2 := by
  simpa [Fintype.sum_bool] using tag_prob F x false

/-- Joint probability that the random tag is one and the circuit on the tagged input succeeds. -/
theorem UniformCircuitFamily.jointProb_randomTag (F : UniformCircuitFamily) (x : List Bool) :
    F.randomTag.onesProb [0, 1] x = F.acceptProb (true :: x) / 2 := by
  simpa [Fintype.sum_bool] using tag_prob F x true

end Cslib.Quantum
