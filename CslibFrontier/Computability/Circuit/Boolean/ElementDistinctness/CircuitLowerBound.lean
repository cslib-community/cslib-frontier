/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (uses the OpenAI matrix exponent proof library)

public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness
public import Cslib.Computability.Circuit.Full
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Circuit.FanIn
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Hard
import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Restore

/-!
# A superlinear Boolean circuit lower bound for element distinctness

For every sufficiently large number of records `m`, deciding distinctness of words of
`2 ⌈log₂ m⌉` bits over the full binary Boolean basis requires `Ω(n (log₂ n)^ε)` gates for a
fixed `ε > 0`, where `n` counts input bits. Gate outputs may be shared without restriction.

[OpenAI, Theorem 2.2][OpenAI2026MatrixMultiplicationExponent] gives a lower bound for exact
trivalent tensor networks testing a batch of lists. We use one list of `2 ^ w` records of
`2 * w` bits over the two-element field. The authors' Lean theorem counts vertices plus exterior
bits. A circuit gives such a network by recomputing all gate equations from a proposed
transcript and summing over transcripts. Acyclicity forces the unique evaluation. Prefix tags
and distinct constant fillers extend the bound to every sufficiently large record count.

## Main result

* `Cslib.Circuits.Boolean.elementDistinctness_circuit_lower_bound`
-/

namespace Cslib.Circuits.Boolean.ElementDistinctness

open Filter OAI.LinearAlgebra.MatrixExponent

/-- An ordinary Boolean DAG of fan-in at most two, with any interpretation of the
gate symbols, has a trivalent network for its graph. Inputs and earlier gate
outputs may each occur in arbitrarily many argument positions. -/
private theorem circuit_dnet {n : ℕ} {σ : Signature} (F : Type) [Field F]
    (C : Circuit σ n 1) (I : Interpretation σ Bool) (h : C.FanInAtMost 2)
    (a : OAI.LinearAlgebra.MatrixExponent.Wire) (i : Fin n ≃ slots a) :
    DNet F a .bit (fun x => C.eval I (bits a x ∘ i) 0) (n + 69 * C.size + 68) := by
  classical
  let source := Cslib.Circuits.Wire.equiv n C.size
  let update (v : Fin n ⊕ Fin C.size → Bool) : Unit ⊕ Fin C.size → Bool :=
    Sum.elim (fun _ => v (source (C.outputs 0))) (fun g =>
      I (C.program.lines g).op fun j => v (source ((C.program.lines g).wires j)))
  have localUpdate : Install.Depends update 2 := by
    rintro (o | g)
    · exact ⟨{source (C.outputs 0)}, by simp, fun _ _ hxy => hxy _ (by simp)⟩
    · let p := fun j => source ((C.program.lines g).wires j)
      refine ⟨Finset.univ.image p, Finset.card_image_le.trans ?_, fun x y hxy => ?_⟩
      · simpa only [Finset.card_univ, Fintype.card_fin] using
          Program.fanInAtMost_iff.mp h g
      · exact congrArg (I (C.program.lines g).op)
          (funext fun j => hxy (p j) (Finset.mem_image_of_mem p (Finset.mem_univ j)))
  let b := word C.size
  let j : Fin C.size ≃ slots b :=
    @Fintype.equivOfCardEq _ _ _ (slotsFintype b)
      (by rw [Fintype.card_fin, card_slots, wd_word])
  let input (x : Val a) := bits a x ∘ i
  let decode (z : Val b) := bits b z ∘ j
  let encode (w : Fin C.size → Bool) := (bits b).symm (w ∘ j.symm)
  have decode_encode (w : Fin C.size → Bool) : decode (encode w) = w := by
    funext k
    simp [decode, encode]
  have decode_inj : Function.Injective decode := by
    intro y z h
    apply (bits b).injective
    funext k
    simpa [decode] using congrFun h (j.symm k)
  let recompute (x : Val a) (z : Val b) (g : Fin C.size) :=
    (C.program.lines g).eval I (input x) (decode z)
  let read (x : Val a) (z : Val b) :=
    Cslib.Circuits.Wire.elim (input x) (decode z) (C.outputs 0)
  let layer (xz : Val (.pair a b)) : Val (.pair .bit b) :=
    (read xz.1 xz.2, encode (recompute xz.1 xz.2))
  have readWire (x : Val a) (z : Val b) (q : Cslib.Circuits.Wire n C.size) :
      bits (.pair a b) (x, z) ((i.sumCongr j) (source q)) =
        Cslib.Circuits.Wire.elim (input x) (decode z) q := by
    cases q <;> rfl
  have layerNet : DNet F (.pair a b) (.pair .bit b) layer (n + 69 * C.size + 68) := by
    have hu := localUpdate.bnet F (.pair a b) (.pair .bit b)
      (i.sumCongr j) ((Equiv.refl Unit).sumCongr j)
    have sizeEq : Fintype.card (Fin n ⊕ Fin C.size) +
        Install.localCost 2 * Fintype.card (Unit ⊕ Fin C.size) =
        n + 69 * C.size + 68 := by
      simp [Install.localCost]
      lia
    rw [sizeEq] at hu
    convert hu using 1
    funext xz
    rcases xz with ⟨x, z⟩
    apply Prod.ext
    · exact (readWire x z _).symm
    · apply decode_inj
      rw [show (layer (x, z)).2 = encode (recompute x z) by rfl, decode_encode]
      funext g
      change recompute x z g = bits (.pair .bit b)
        ((bits (.pair .bit b)).symm _) (.inr (j g))
      rw [Equiv.apply_symm_apply]
      simp only [Function.comp_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr,
        Equiv.symm_apply_apply]
      exact congrArg (I (C.program.lines g).op)
        (funext fun k => (readWire x z _).symm)
  let actual (x : Val a) := encode (C.program.eval I (input x))
  have feedback (x : Val a) (z : Val b) :
      (layer (x, z)).2 = z ↔ z = actual x := by
    change encode (recompute x z) = z ↔ _
    constructor
    · intro hz
      have hrun := C.program.eq_eval_of_forall_lines_eval I (input x) (decode z)
        fun g => congrFun ((decode_encode _).symm.trans (congrArg decode hz)) g
      exact decode_inj (hrun.trans (decode_encode _).symm)
    · rintro rfl
      apply congrArg encode
      funext g
      change (C.program.lines g).eval I (input x) (decode (encode _)) = _
      rw [decode_encode, C.program.lines_eval]
  have read_actual (x : Val a) :
      (layer (x, actual x)).1 = C.eval I (input x) 0 := by
    change Cslib.Circuits.Wire.elim _ (decode (encode _)) _ = _
    rw [decode_encode]
    rfl
  obtain ⟨v, hv, graph⟩ := layerNet
  refine ⟨v, hv, ?_⟩
  convert graph.trace using 1
  funext x y
  symm
  rw [Finset.sum_eq_single (actual x)]
  · simp only [Prod.ext_iff, read_actual, feedback, and_true]
    rfl
  · intro z _ hz
    simp [Prod.ext_iff, feedback, hz]
  · simp

private noncomputable def records (w : ℕ) :=
  (Layout.exists_tree (word (2 * w)) w).choose

private def wordSlots (k : ℕ) : Fin k ≃ slots (word k) :=
  ((Transcript.positions (word k)).trans (finCongr (wd_word k))).symm

/-- Row-major bit numbering for the single-list tensor. -/
private noncomputable def singleListSlots (w : ℕ) : Fin (2 ^ w * (2 * w)) ≃ slots (lists w 1) :=
  finProdFinEquiv.symm.trans (((Equiv.refl _).prodCongr (wordSlots (2 * w))).trans
    ((records w).positions.trans (Equiv.sumEmpty _ Empty).symm))

/-- The Boolean circuit problem on these bits accepts precisely the tensor's
distinct lists. -/
private theorem elementDistinctness_singleList (w : ℕ) (x : Val (lists w 1)) :
    elementDistinctness (2 ^ w) (2 * w) (bits (lists w 1) x ∘ singleListSlots w) =
      decide (flatten w x.1).Nodup := by
  classical
  let asBits : Val (word (2 * w)) ≃ (Fin (2 * w) → Bool) :=
    (bits _).trans ((wordSlots (2 * w)).symm.arrowCongr (Equiv.refl Bool))
  have hblocks : Cslib.BitString.block (bits (lists w 1) x ∘ singleListSlots w) =
      asBits ∘ (records w).read x.1 := by
    funext r b
    simp only [Cslib.BitString.block_apply, Function.comp_apply, singleListSlots,
      Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Equiv.refl_apply,
      Prod.map_apply]
    change bits (tree w (word (2 * w))) x.1 ((records w).positions (r, wordSlots (2 * w) b)) =
      bits (word (2 * w)) ((records w).read x.1 r) (wordSlots (2 * w) b)
    simp [Layout.read]
  apply Bool.eq_iff_iff.mpr
  rw [elementDistinctness, decide_eq_true_eq, decide_eq_true_eq, hblocks,
    ← (Layout.exists_tree (word (2 * w)) w).choose_spec x.1, List.nodup_ofFn]
  exact asBits.injective.of_comp_iff _

/-- Pinning the output to one represents the indicator of a single distinct list. -/
private theorem realizes_of_circuit {w : ℕ} {σ : Signature}
    (C : Circuit σ (2 ^ w * (2 * w)) 1) (I : Interpretation σ Bool) (hfan : C.FanInAtMost 2)
    (hC : C.Computes I (single (elementDistinctness (2 ^ w) (2 * w)))) :
    ∃ m ≤ 2 * listBits w + 69 * C.size + 69, Realizes (ZMod 2) w 1 m := by
  obtain ⟨v, hv, graph⟩ := circuit_dnet (ZMod 2) C I hfan (lists w 1) (singleListSlots w)
  have pin := Net.table (F := ZMod 2) .bit .unit (fun b _ => if b then 1 else 0) (by decide)
  have heval (x : Val (lists w 1)) :
      C.eval I (bits (lists w 1) x ∘ singleListSlots w) 0 = decide (flatten w x.1).Nodup := by
    rw [hC, single_apply, elementDistinctness_singleList]
  refine ⟨v + 1 + 1 * listBits w, ?_, v + 1, ?_, rfl⟩
  · rw [one_mul, listBits, Nat.mul_comm (2 * w)]
    lia
  · simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      heval, decide_eq_true_eq, distinctPower, mul_one] using graph.comp pin

private theorem dyadic_elementDistinctness_circuit_lower_bound :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ᶠ w : ℕ in atTop,
      let n := 2 ^ w * (2 * w)
      ∀ {σ : Signature} (C : Circuit σ n 1) (I : Interpretation σ Bool),
        C.FanInAtMost 2 → C.Computes I (single (elementDistinctness (2 ^ w) (2 * w))) →
        c * n * (Real.logb 2 n) ^ ε < C.size := by
  obtain ⟨ε, hε, hard⟩ := BatchDescent.manyList_full (ZMod 2)
  refine ⟨ε, (138 * (3 : ℝ) ^ ε)⁻¹, hε, by positivity, ?_⟩
  have grow : Tendsto (fun w : ℕ => (w : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [hard, eventually_ge_atTop 1, grow.eventually_ge_atTop 142]
    with w bound hw hlarge
  dsimp only
  intro σ C I hfan hC
  let n := 2 ^ w * (2 * w)
  have hn : listBits w = n := Nat.mul_comm ..
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 0 < n by dsimp [n]; positivity)
  obtain ⟨m, hm, hnet⟩ := realizes_of_circuit C I hfan hC
  have range : (1 : ℝ) ≤ (2 : ℝ) ^ ((w : ℝ) ^ (1 + ε)) :=
    Real.one_le_rpow (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have volume := bound 1 m le_rfl (by simpa only [Nat.cast_one] using range) hnet
  rw [Nat.cast_one, one_mul, hn] at volume
  rw [hn] at hm
  have cost : (m : ℝ) ≤ 2 * n + 69 * (C.size : ℝ) + 69 := by exact_mod_cast hm
  have gates : (n : ℝ) * (w : ℝ) ^ ε < 138 * (C.size : ℝ) := by
    nlinarith only [volume, cost, hn1, mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg n)]
  have hn_bound : n ≤ 2 ^ (3 * w) := calc
    n ≤ 2 ^ w * 2 ^ (2 * w) := Nat.mul_le_mul_left _ (Nat.lt_two_pow_self.le)
    _ = 2 ^ (3 * w) := by rw [← pow_add]; congr 1; lia
  have hlog : Real.logb 2 n ≤ 3 * (w : ℝ) := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith : (0 : ℝ) < n)
      (show (n : ℝ) ≤ (2 : ℝ) ^ (3 * w) by exact_mod_cast hn_bound)
    simpa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using this
  have hpow := Real.rpow_le_rpow (Real.logb_nonneg (by norm_num) hn1) hlog hε.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg w)] at hpow
  change (138 * (3 : ℝ) ^ ε)⁻¹ * n * (Real.logb 2 n) ^ ε < C.size
  calc
    _ ≤ (138 * (3 : ℝ) ^ ε)⁻¹ * n * ((3 : ℝ) ^ ε * (w : ℝ) ^ ε) := by gcongr
    _ = (n : ℝ) * (w : ℝ) ^ ε / 138 := by
      have : 0 < (3 : ℝ) ^ ε := by positivity
      field_simp
    _ < C.size := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 138)).mpr (by linarith)

open Cslib.BitString (block blocksEquiv)

/-- Extend original payloads with zeroes. The first bit distinguishes originals from fillers. -/
private def taggedWord {α : Type} {b k : ℕ} (zero one : α) :
    (Fin b → α) ⊕ (Fin k → α) → Fin (k + 1) → α
  | .inl x => Fin.cons zero fun j => if h : j.val < b then x ⟨j, h⟩ else zero
  | .inr y => Fin.cons one y

private theorem taggedWord_injective {b k : ℕ} (hb : b ≤ k) :
    Function.Injective (taggedWord (b := b) (k := k) false true) := by
  rintro (x | x) (y | y) h
  · apply congrArg Sum.inl
    funext j
    simpa [taggedWord, j.isLt] using congrFun h (Fin.castLE hb j).succ
  · simpa [taggedWord] using congrFun h 0
  · simpa [taggedWord] using congrFun h 0
  · apply congrArg Sum.inr
    funext j
    simpa [taggedWord] using congrFun h j.succ

/-- A circuit for `m` records of width `k` gives one for `a ≤ m` records of width
`b < k` using at most two additional gates. The `m - a` filler records have distinct
`k - 1`-bit payloads and carry the opposite tag from the original records. -/
private theorem exists_elementDistinctness_restriction {a b m k : ℕ} (ha : a ≤ m) (hb : b < k)
    (hm : m - a ≤ 2 ^ (k - 1)) (C : Circuit (fullSignature 2 Bool) (m * k) 1)
    (hC : C.Computes fullInterpretation (single (elementDistinctness m k))) :
    ∃ D : Circuit (fullSignature 2 Bool) (a * b) 1, D.size ≤ C.size + 2 ∧
      D.Computes fullInterpretation (single (elementDistinctness a b)) := by
  classical
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le ha
  cases k with
  | zero => lia
  | succ k =>
    obtain ⟨code⟩ : Nonempty (Fin e ↪ (Fin k → Bool)) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hm)
    let rows : Fin a ⊕ Fin e → (Fin b → Fin (a * b) ⊕ Bool) ⊕ (Fin k → Fin (a * b) ⊕ Bool) :=
      Sum.map (fun r j => .inl (finProdFinEquiv (r, j))) (fun r j => .inr (code r j))
    let feed : Fin ((a + e) * (k + 1)) → Fin (a * b) ⊕ Bool :=
      blocksEquiv.symm fun r => taggedWord (.inr false) (.inr true) (rows (finSumFinEquiv.symm r))
    obtain ⟨pins, hpins, hsize⟩ := (Boolean.substituteCircuit feed).exists_simulation_le
      (fullInterpretation_simulatesWithCost Boolean.interpretation Boolean.arity_le_two)
    refine ⟨C.comp pins, ?_, ?_⟩
    · rw [Circuit.size_comp]
      have : pins.size ≤ 2 := by simpa using hsize
      lia
    intro x
    rw [Circuit.eval_comp, hpins, Boolean.eval_substituteCircuit, hC]
    apply congrArg (fun v : Bool => fun _ : Fin 1 => v)
    have hblocks : block (Boolean.substitute feed x) =
        (taggedWord false true ∘ Sum.map (block x) code) ∘ finSumFinEquiv.symm := by
      funext r j
      change Sum.elim x id (block (blocksEquiv.symm _) r j) = _
      rw [Cslib.BitString.block_blocksEquiv_symm]
      simp only [Function.comp_apply]
      cases hrow : finSumFinEquiv.symm r with
      | inl s =>
        refine Fin.cases ?_ (fun d => ?_) j
        · rfl
        · by_cases hd : d.val < b <;> simp [rows, taggedWord, hd]
      | inr s =>
        refine Fin.cases ?_ (fun d => ?_) j <;> rfl
    change decide (Function.Injective (block (Boolean.substitute feed x))) =
      decide (Function.Injective (block x))
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, decide_eq_true_eq, hblocks, Equiv.injective_comp,
      (taggedWord_injective (Nat.le_of_lt_succ hb)).of_comp_iff,
      Sum.map_injective, and_iff_left code.injective]

end Cslib.Circuits.Boolean.ElementDistinctness

namespace Cslib.Circuits.Boolean

open Filter ElementDistinctness

private theorem log_cost_le_of_bits_le {ε : ℝ} (hε : 0 < ε) {n N : ℕ}
    (hn : 8 ≤ n) (hN : 1 ≤ N) (hbits : N ≤ 8 * n) :
    (N : ℝ) * (Real.logb 2 N) ^ ε ≤ (8 * (2 : ℝ) ^ ε) * (n * (Real.logb 2 n) ^ ε) := by
  have hsq : (N : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast hbits.trans (show 8 * n ≤ n ^ 2 by rw [pow_two]; gcongr)
  have hlog : Real.logb 2 N ≤ 2 * Real.logb 2 n := by
    simpa only [Real.logb_pow, Nat.cast_ofNat] using
      Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hN : (0 : ℝ) < N) hsq
  have h₁ : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) (by exact_mod_cast hN)
  have h₂ : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by lia : 1 ≤ n))
  calc
    (N : ℝ) * (Real.logb 2 N) ^ ε ≤ (8 * (n : ℝ)) * (2 * Real.logb 2 n) ^ ε :=
      mul_le_mul (by exact_mod_cast hbits) (Real.rpow_le_rpow h₁ hlog hε.le)
        (Real.rpow_nonneg h₁ _) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num) h₂]; ring

/-- For every sufficiently large number of records `m`, element distinctness on words of
`2 ⌈log₂ m⌉` bits needs `Ω(n (log₂ n)^ε)` gates over the full binary Boolean basis,
where `n = 2 m ⌈log₂ m⌉` is the total input length. -/
public theorem elementDistinctness_circuit_lower_bound :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      let k := 2 * Nat.clog 2 m
      let n := m * k
      ∀ C : Circuit (fullSignature 2 Bool) n 1,
        C.Computes fullInterpretation (single (elementDistinctness m k)) →
        c * n * (Real.logb 2 n) ^ ε < C.size := by
  obtain ⟨ε, c, hε, hc, dyadic⟩ := dyadic_elementDistinctness_circuit_lower_bound
  let width (m : ℕ) := Nat.log 2 m - 1
  have grow : Tendsto width atTop atTop := tendsto_atTop.mpr fun r => by
    filter_upwards [eventually_ge_atTop (2 ^ (r + 1))] with m hm
    have := Nat.le_log_of_pow_le (by decide : 1 < 2) hm
    dsimp only [width]
    lia
  have scaled : Tendsto (fun w : ℕ => c * (w : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  refine ⟨ε, c / (24 * (2 : ℝ) ^ ε), hε, by positivity, ?_⟩
  filter_upwards [grow.eventually dyadic, grow.eventually_ge_atTop 2,
    (scaled.comp grow).eventually_ge_atTop 2, eventually_ge_atTop 2] with m hsmall hw hlarge hm
  dsimp only
  intro C hC
  let w := width m
  let k := 2 * Nat.clog 2 m
  let n := 2 ^ w * (2 * w)
  change 2 ≤ w at hw
  change (2 : ℝ) ≤ c * w at hlarge
  have hfloor : Nat.log 2 m = w + 1 := by dsimp [w, width] at hw ⊢; lia
  have ceil_lo := Nat.log_le_clog 2 m
  have ceil_hi := Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide : 1 < 2) m).le
  rw [hfloor] at ceil_lo ceil_hi
  have ha : 2 ^ w ≤ m := (Nat.pow_le_pow_right (by decide : 0 < 2)
    (show w ≤ Nat.log 2 m by lia)).trans (Nat.pow_log_le_self 2 (by lia))
  have hk : 2 * w < k := by dsimp [k]; lia
  have hmcode : m ≤ 2 ^ (k - 1) := (Nat.le_pow_clog (by decide : 1 < 2) m).trans
    (Nat.pow_le_pow_right (by decide) (show Nat.clog 2 m ≤ k - 1 by dsimp [k]; lia))
  obtain ⟨D, hsize, hD⟩ := exists_elementDistinctness_restriction ha hk
    ((Nat.sub_le m _).trans hmcode) C hC
  have hfan : D.FanInAtMost 2 :=
    Circuit.fanInAtMost_of_arity_le (fun op => by cases op <;> simp [fullSignature]) D
  have hard : c * n * (Real.logb 2 n) ^ ε < D.size := hsmall D fullInterpretation hfan hD
  have hpad : m < 2 ^ w * 4 := by
    simpa [hfloor, pow_succ, Nat.mul_assoc] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) m
  have hbits : m * k ≤ 8 * n := calc
    m * k ≤ (2 ^ w * 4) * (2 * (2 * w)) := Nat.mul_le_mul hpad.le (by dsimp [k]; lia)
    _ = 8 * n := by dsimp [n]; ring
  have hn : 8 ≤ n := calc
    8 ≤ 2 ^ 2 * (2 * 2) := by decide
    _ ≤ n := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hw) (Nat.mul_le_mul_left 2 hw)
  have hlog : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast (by lia : 0 < n)), Real.rpow_one]
    exact_mod_cast (by lia : 2 ≤ n)
  have hwn : w ≤ n := by
    dsimp only [n]
    calc w ≤ 2 * w := by lia
         _ ≤ 2 ^ w * (2 * w) := Nat.le_mul_of_pos_left _ (by positivity)
  have hneed : (2 : ℝ) ≤ c * n * (Real.logb 2 n) ^ ε := calc
    2 ≤ c * w := hlarge
    _ ≤ c * n := by gcongr
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hlog hε.le)
  have hsize' : (D.size : ℝ) ≤ C.size + 2 := by exact_mod_cast hsize
  have hgate : 1 ≤ (C.size : ℝ) := by
    have hpos : 0 < (C.size : ℝ) := by linarith
    exact_mod_cast (Nat.cast_pos.mp hpos : 1 ≤ C.size)
  have hpos : 0 < m * k := Nat.mul_pos (by lia) (by lia)
  have compare := log_cost_le_of_bits_le hε hn hpos hbits
  calc
    c / (24 * (2 : ℝ) ^ ε) * (m * k : ℕ) * (Real.logb 2 (m * k : ℕ)) ^ ε
      ≤ c / (24 * (2 : ℝ) ^ ε) * ((8 * (2 : ℝ) ^ ε) * (n * (Real.logb 2 n) ^ ε)) := by
        rw [mul_assoc]; gcongr
    _ = c * n * (Real.logb 2 n) ^ ε / 3 := by
      have : (2 : ℝ) ^ ε ≠ 0 := ne_of_gt (by positivity)
      field_simp
      ring
    _ < C.size := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr (by linarith)

end Cslib.Circuits.Boolean
