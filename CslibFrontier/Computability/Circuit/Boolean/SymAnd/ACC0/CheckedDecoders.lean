/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.CompressionPolyTime
import CslibFrontier.Computability.Circuit.Boolean.ACC0.CodeLength

/-!
# Checked `ACC⁰` decoders for polynomial-time functions under `P ⊆ ACC⁰`

If every language in `P/poly` has polynomial-size `AC⁰[m]` circuits of depth `d`, then every
function `F` computed in polynomial time on inputs `(x, i)`, with `|i| = a x`, has checked
decoders (`Cslib.Circuits.Boolean.SymAnd.exists_checkedDecoders`): a
`Cslib.Circuits.Boolean.SymAnd.CheckedACC0Decoders`, polynomial-time families of a depth-`(d + 5)`
check circuit `C₁ (x, e)` and a depth-`(d + 2)` decoder `D (x, e)` on the `a x` bits of `i`, such
that `D (x, e)` computes the bits of `F (x, i)` whenever `C₁ (x, e)` is unsatisfiable, and some `e`
of polynomial length makes `C₁ (x, e)` unsatisfiable. This is the
compression step of [Williams2014], Lemma 3.1, for decoders computed in polynomial time; the
construction is in `CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.Compression`.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.exists_checkedDecoders`: checked decoders for a polynomial-time
  function, assuming `P/poly ⊆ AC⁰[m]` at a constant depth.

## References

* [R. Williams, *Non-Uniform ACC Circuit Lower Bounds*, July 31, 2012 version, Lemma 3.1]
  [Williams2014]
-/

public section

namespace Cslib.Circuits.Boolean.SymAnd

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInPolyTime
  Cslib.Circuits
  Cslib.Circuits.Boolean Cslib.Complexity Cslib.Complexity.CookLevin Cslib.Logic.PL
  Compression

/-- **Checked `ACC⁰` decoders for polynomial-time functions** ([Williams2014], Lemma 3.1, for
decoders computed in polynomial time). If every language in `P/poly` has polynomial-size
`AC⁰[m]` circuits of depth `d`, then for every polynomial-time `F` and polynomial-time widths
`a`, `J`, there are checked decoders on `a x` inputs, with check circuits of depth `d + 5` and
decoders of depth `d + 2`, such that `D (x, e)` computes the first `J x` bits of `F (x, i)`
whenever `C₁ (x, e)` is unsatisfiable, and for every `x` some `e` of the certificate length,
polynomial in `|x|`, makes `C₁ (x, e)` unsatisfiable. -/
theorem exists_checkedDecoders {m d : ℕ} (hm : 0 < m)
    (hP : ∀ L ∈ PPoly, ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n,
      ∃ C : Circuit Unbounded.extSignature n 1,
        C.Computes (Unbounded.extInterpretation (modGate m)) (single (L.slice n)) ∧
        C.depth ≤ d ∧ C.size ≤ s n)
    {a J : List Bool → ℕ} (ha : ComputableInPolyTime a encBits encUnary)
    (hJ : ComputableInPolyTime J encBits encUnary)
    {F : List Bool × List Bool → List Bool}
    (hF : ComputableInPolyTime F (encPair encBits encBits) encBits) :
    ∃ R : CheckedACC0Decoders (d + 5) (d + 2) a a J,
      (∀ x e, ⟨a x, R.check (x, e)⟩ ∉
          SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) →
        ∀ (i : BitString (a x)) (j : Fin (J x)),
          (R.decoder (x, e)).eval (Unbounded.extInterpretation (modGate m)) i j =
            (F (x, List.ofFn i)).getD j false) ∧
      ∀ x, ∃ e : List Bool, e.length = R.certLength x ∧
        ⟨a x, R.check (x, e)⟩ ∉
          SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) := by
  -- a machine computing the bits of `F`
  obtain ⟨t, s₀, ht, -, k, State, hfin, tm, htm⟩ := computableInPolyTime_queryBit hJ hF
  obtain ⟨cT, dT, ht⟩ := polynomiallyBounded_iff_le.mp ht
  have := Fintype.ofFinite State
  classical
  have hrun : ∀ w, (tm.runFrom (tm.initCfg w) (cT * (w.length + 1) ^ dT)).state = none ∧
      (tm.runFrom (tm.initCfg w) (cT * (w.length + 1) ^ dT)).output = [queryBit J F w] :=
    fun w => (htm w).runFrom_of_le (ht _)
  obtain ⟨cI, hI⟩ := exists_index_lt_of_determined k State
  set W := width cT dT cI a J
  have hW := computableInPolyTime_width cT dT cI ha hJ
  have hout : ∀ x, outVar (k := k) (State := State) cT dT a J x ≤ W x := fun x =>
    (index_lt_width hI (Or.inr (Or.inl ⟨_, le_rfl, _, Feature.out_mem_basic _, rfl⟩))).le
  -- circuits for the run bits, with `frame x` hardwired
  obtain ⟨L, hL, hLiff⟩ := PPoly.exists_of_polyTime
    (computableInPolyTime_runBit tm cT dT hJ hW)
  obtain ⟨s, hs, hC⟩ := hP L hL
  obtain ⟨cG, kG, hG⟩ := Unbounded.exists_hardwirePrefix_code_le hm hs hC
  -- the code-length budget of the guessed circuit
  let nG : List Bool → ℕ := fun x => J x + W x + a x
  let ℓ : List Bool → ℕ := fun x => 2 * (cG * ((2 * x.length + 1) + nG x + 1) ^ kG) + 1
  have hℓ : ComputableInPolyTime ℓ encBits encUnary := by
    have hlen : ComputableInPolyTime (fun x : List Bool => x.length) encBits encUnary :=
      length_bits
    dsimp only [ℓ, nG]
    fun_prop
  obtain ⟨cℓ, kℓ, hℓ_le⟩ := hℓ.polyBounded_length.exists_le
  refine ⟨{ certLength := ℓ, slack := cℓ + kℓ
            check := fun p => checkCircuit tm cT dT cI a J (d + 1) p.1 p.2
            decoder := fun p =>
              decoderCircuit (k := k) (State := State) cT dT cI a J (d + 1) p.1 p.2
            certLength_polyTime := hℓ
            certLength_le := fun x => ?_
            check_polyTime := computableInPolyTime_checkCircuit_code tm cT dT cI ha hJ (d + 1)
            decoder_polyTime :=
              computableInPolyTime_decoderCircuit_code k State cT dT cI ha hJ (d + 1) hout
            depth_check_le := fun p => ?_
            depth_decoder_le := fun p => ?_ },
    fun x e hx i j => eval_decoderCircuit_of_not_mem m hrun hI (d + 1) x e hx i j, fun x => ?_⟩
  · have h := hℓ_le x
    simp only [encUnary_apply, List.length_replicate] at h
    refine h.trans ?_
    have h1 : 1 ≤ (encBits x).length + 1 := by omega
    calc cℓ * ((encBits x).length + 1) ^ kℓ
        ≤ (cℓ + kℓ) * ((encBits x).length + 1) ^ (cℓ + kℓ) :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right h1 (by omega))
      _ = (cℓ + kℓ) * (x.length + 1) ^ (cℓ + kℓ) := rfl
  · exact (depth_checkCircuit_le _ _ _).trans (by omega)
  · exact (depth_decoderCircuit_le _ _ _).trans (by omega)
  · -- the guessed circuit: a circuit for the run bits with `frame x` hardwired
    obtain ⟨G, hGeval, hGdepth, hGcode⟩ := hG (frame x) (nG x)
    set u := Circuit.encCode Unbounded.encExtOp G.code
    have hfl : (frame u).length ≤ ℓ x := by
      rw [length_frame]
      rw [length_frame] at hGcode
      dsimp only [ℓ]
      omega
    refine ⟨frame u ++ List.replicate (ℓ x - (frame u).length) false, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate]
      omega
    · have hdec : decodeExtWitness (d + 1) (J x + W x + a x)
          (frame u ++ List.replicate (ℓ x - (frame u).length) false) = some G :=
        decodeExtWitness_frame_append G hGdepth _
      refine checkCircuit_not_mem m hI (d + 1) x _ fun z => ?_
      rw [guessed, hdec, Option.getD_some, Bool.eq_iff_iff, hGeval]
      exact (hLiff _).symm

end Cslib.Circuits.Boolean.SymAnd
