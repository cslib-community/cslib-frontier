/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.InitializedEvaluatorCorrect
import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearchSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Quantitative selected-parameter bounds for schedule search

These estimates separate linear bank and assignment-capacity storage from logarithmic metadata.
In particular, the chunk width used at each stack level is bounded by the binary block width,
not by the block width itself. This distinction prevents a spurious horizon-times-block term.
The final estimate bounds the uniform schedule allowance of the initialized evaluator.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleSearch

open MultiTapeTM Cslib.TreeEval.Ary.Packed
open QueryReplay MultiTapeNTM.ChoiceTable

/-- A fixed-machine linear bound on the complete encoded block-value width. -/
@[expose] def widthConstant (k s : ℕ) : ℕ := 7 * k + (s + 1).size + 4

/-- Positive blocks absorb the fixed header overhead into a fixed multiplicative constant. -/
theorem width_le_mul (k s : ℕ) {b : ℕ} (hb : 0 < b) :
    Encoding.width k s b ≤ widthConstant k s * b := by
  have := Encoding.width_le k s b
  have := Nat.le_mul_of_pos_right ((s + 1).size + 3) hb
  simp only [widthConstant, Nat.add_mul, one_mul] at *; omega

/-- Measuring the encoded value width adds only a fixed number of bits to the block width. -/
theorem width_size_le (k s : ℕ) {b : ℕ} (hb : 0 < b) :
    (Encoding.width k s b).size ≤ (widthConstant k s).size + b.size :=
  (Nat.size_le_size (width_le_mul k s hb)).trans (Nat.size_mul_le _ _)

/-- The selected chunk width is logarithmic in the block width, uniformly in the horizon. -/
theorem selected_chunkWidth_le (k s : ℕ) {b : ℕ} (hb : 0 < b) :
    chunkWidth (k * 3 + 1) (Encoding.width k s b) ≤
      (k * 3 + 1).size + (widthConstant k s).size + b.size :=
  ((Nat.size_mul_le _ _).trans (Nat.add_le_add_left (width_size_le k s hb) _)).trans_eq
    (Nat.add_assoc _ _ _).symm

/-- This is the logarithmic estimate needed inside the horizon-dependent stack term. -/
theorem horizon_chunkWidth_le (k s q : ℕ) {b : ℕ} (hb : 0 < b) :
    q * (chunkWidth (k * 3 + 1) (Encoding.width k s b) + 1) ≤
      ((k * 3 + 1).size + (widthConstant k s).size + 1) * q * (b.size + 1) := by
  have hscalar : chunkWidth (k * 3 + 1) (Encoding.width k s b) + 1 ≤
      ((k * 3 + 1).size + (widthConstant k s).size + 1) * (b.size + 1) := by
    have := selected_chunkWidth_le k s hb
    have := Nat.le_mul_of_pos_left b.size
      (by omega : 0 < (k * 3 + 1).size + (widthConstant k s).size + 1)
    rw [Nat.mul_add_one (_ + 1)]; omega
  simpa only [Nat.mul_assoc, Nat.mul_left_comm q] using Nat.mul_le_mul_left q hscalar

/-- The selected raw evaluator contributes linear bank storage and logarithmic storage per level.
The context and supplier allowances are retained with their existing constant coefficients. -/
theorem selected_queryStateBound_le (k s : ℕ) : ∃ C, ∀ contextBits supplierBits b q : ℕ,
    0 < b →
    RawController.Query.queryStateBound contextBits
      (fieldModulus (k * 3 + 1) (Encoding.width k s b)) (k * 3 + 1)
      (chunkCount (k * 3 + 1) (Encoding.width k s b)) q supplierBits ≤
      4 * contextBits + supplierBits + C * (b + q * (b.size + 1) + 1) := by
  let d := k * 3 + 1
  let A := widthConstant k s
  let L := d.size + A.size + 1
  refine ⟨200 * (d + 1) * (A + L + d.size + 1) + 4, fun contextBits supplierBits b q hb => ?_⟩
  have hraw := RawController.Query.queryStateBound_packed_le contextBits supplierBits
    (d := d) (b := Encoding.width k s b) (H := q) (by dsimp only [d]; omega)
    (Encoding.width_pos k s b)
  have hwidth := width_le_mul k s hb
  have hstack := horizon_chunkWidth_le k s q hb
  have hinner : Encoding.width k s b +
      q * (chunkWidth d (Encoding.width k s b) + 1) + d.size + 1 ≤
      (A + L + d.size + 1) * (b + q * (b.size + 1) + 1) := by
    let R := b + q * (b.size + 1) + 1
    have hw : Encoding.width k s b ≤ A * R :=
      hwidth.trans (Nat.mul_le_mul_left A (by dsimp only [R]; omega))
    have hq : q * (chunkWidth d (Encoding.width k s b) + 1) ≤ L * R :=
      hstack.trans ((Nat.mul_assoc L q _).le.trans (Nat.mul_le_mul_left L (by dsimp [R]; omega)))
    have hc : d.size + 1 ≤ (d.size + 1) * R :=
      Nat.le_mul_of_pos_right _ (by dsimp only [R]; omega)
    exact (show _ ≤ A * R + L * R + (d.size + 1) * R by omega).trans_eq (by dsimp only [R]; ring)
  have hmul := Nat.mul_le_mul_left (200 * (d + 1)) hinner
  have h4 := Nat.le_mul_of_pos_right 4 (by omega : 0 < b + q * (b.size + 1) + 1)
  dsimp only [d] at hraw hmul ⊢
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

/-- The selected assignment capacity is a power of two with its exact binary length charged. -/
theorem assignment_limit_size (d B : ℕ) :
    ((2 ^ chunkWidth d B) ^ (d * chunkCount d B)).size =
      d * (chunkCount d B * chunkWidth d B) + 1 := by
  rw [← pow_mul, Nat.size_pow, Nat.mul_comm (chunkWidth d B), Nat.mul_assoc]

/-- Capacity bits are linear in the value width; the number of assignments is never charged. -/
theorem assignment_limit_size_le {d B : ℕ} (hd : 0 < d) (hB : 0 < B) :
    ((2 ^ chunkWidth d B) ^ (d * chunkCount d B)).size ≤
      d * (B + chunkWidth d B) + 1 := by
  rw [assignment_limit_size]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left d (chunkCount_mul_lt hd hB).le) 1

/-- A full interpolation point has linear field-cell storage at the selected parameters. -/
theorem selected_point_cost_le {d B : ℕ} (hd : 0 < d) (hB : 0 < B) :
    d * chunkCount d B * (2 * (fieldModulus d B).size + 1) ≤
      17 * d * (B + chunkWidth d B) := by
  have h := Nat.mul_le_mul_left d (chunkCount_mul_framed_fieldModulus_size_le hd hB 2)
  rw [← Nat.mul_assoc, ← Nat.mul_assoc] at h
  exact h.trans (Nat.mul_le_mul_right _ (by omega))

/-- Native parameter initialization already supplies a uniform binary metadata-size estimate. -/
theorem prepared_metadata_le (k s : ℕ) : ∃ C, ∀ N b σ q : ℕ,
    (Initializer.encMetadata ((Initializer.prepare k s (N, b, σ, q)).1)).length ≤
      C * (N.size + b.size + σ.size + q.size + 1) := by
  obtain ⟨c, hc⟩ := MultiTapeTM.ComputableInSpace.length_le (Initializer.prepare_inSpace k s)
  refine ⟨4 * c, fun N b σ q => ?_⟩
  have h := hc (N, b, σ, q)
  simp only [Initializer.encState, Initializer.encArgs, Initializer.prepare,
    length_encPair, length_encNat_eq_size] at h ⊢
  rw [Nat.mul_comm 4 c, Nat.mul_assoc]
  refine Nat.le_trans ?_ (h.trans (Nat.mul_le_mul_left c ?_)) <;> omega

/-- Binary selected interpolation metadata retains the assignment capacity only once. -/
theorem selected_metadataSpace_le (N b σ q d B : ℕ) (hd : 0 < d) (hB : 0 < B) :
    ConcreteSupplier.metadataSpace N b σ q (chunkWidth d B) (2 ^ chunkWidth d B)
      ((2 ^ chunkWidth d B) ^ (d * chunkCount d B)) (fieldModulus d B) d
      (chunkCount d B) ≤
      100 * (d + 1) * (N.size + b.size + σ.size + q.size + B + chunkWidth d B + d.size + 1) := by
  have hr := chunkCount_le hd hB
  have hrsize := Nat.size_le_size hr
  have hBsize := Nat.size_le_self B
  have hmSize := Nat.size_le_self (chunkWidth d B)
  have hstride := Nat.size_mul_le (chunkCount d B) (chunkWidth d B)
  have hpoint := Nat.size_mul_le d (chunkCount d B)
  have hp := fieldModulus_size_le hd hB
  have hlimit := assignment_limit_size_le hd hB
  simp only [ConcreteSupplier.metadataSpace, QueryGate.encParams, Interpolation.encContext_apply,
    Interpolation.encContextFields, encNat3, length_encPair, length_encNat_eq_size]
  rw [Nat.size_pow (n := chunkWidth d B), show (encList encNat []).length = 0 from rfl,
    Nat.mul_assoc 100, Nat.add_mul d 1, one_mul]
  have hdB := Nat.mul_le_mul_left d (show B + chunkWidth d B ≤
    N.size + b.size + σ.size + q.size + B + chunkWidth d B + d.size + 1 by omega)
  omega

private theorem context_le_metadataSpace (N b σ q m alphabet limit p d r : ℕ) :
    (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length ≤
      ConcreteSupplier.metadataSpace N b σ q m alphabet limit p d r := by
  simp only [ConcreteSupplier.encContext, ConcreteSupplier.metadataSpace, QueryGate.encParams,
    Interpolation.encContext_apply,
    Interpolation.encContextFields, encNat3, length_encPair]
  omega

/-- One selected candidate has linear bank storage and logarithmic storage per tree level. -/
theorem initialized_allowance_le (k s : ℕ) (Q : Type) : ∃ C, ∀ N b σ q : ℕ, 0 < b →
    InitializedEvaluator.allowance k s Q N b σ q ≤
      C * (b + q * (b.size + 1) + N.size + σ.size + 1) := by
  let d := k * 3 + 1
  let A := widthConstant k s
  let M := d.size + A
  let H := 100 * (d + 1) * (A + M + d.size + 2)
  let P := 17 * d * (A + M)
  obtain ⟨row, hrow_eq⟩ :
      ∃ row, Fintype.card (Option (Fin k)) * (2 * Nat.card SignType + 1) = row := ⟨_, rfl⟩
  obtain ⟨cards, hcards_eq⟩ :
      ∃ cards, Nat.card (Option Q) + Nat.card OutputTrack = cards := ⟨_, rfl⟩
  let replay := 4 * M + 3 * A + 8 + 2 * row + 10 + 1024 * (k + 1) * (cards + 3)
  let reply := 48 * (H + 2 * P + 1) + 16 * A + 3 * P + replay + 14
  obtain ⟨ci, hci⟩ := prepared_metadata_le k s
  obtain ⟨cr, hcr⟩ := selected_queryStateBound_le k s
  let init := 16 * ci + 16 + 192 * (d + 1) * (2 * A + d.size)
  refine ⟨init + 4 * H + reply + cr + 2, fun N b σ q hb => ?_⟩
  let B := Encoding.width k s b
  let m := chunkWidth d B
  let r := chunkCount d B
  let p := fieldModulus d B
  let alphabet := 2 ^ m
  let limit := alphabet ^ (d * r)
  let R := b + q * (b.size + 1) + N.size + σ.size + 1
  have hd : 0 < d := by dsimp only [d]; omega
  have hB : 0 < B := Encoding.width_pos k s b
  have hR : 0 < R := by dsimp only [R]; omega
  have hbs := Nat.size_le_self b
  have hqs := Nat.size_le_self q
  have hqmul : q ≤ q * (b.size + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hargs : N.size + b.size + σ.size + q.size + 1 ≤ R := by
    dsimp only [R]; omega
  have hbR : b ≤ R := by dsimp only [R]; omega
  have hBR : B ≤ A * R := (width_le_mul k s hb).trans (Nat.mul_le_mul_left A hbR)
  have hmR : m ≤ M * R := by
    have hm := chunkWidth_le d B
    have hc := Nat.le_mul_of_pos_right d.size hR
    rw [show M * R = d.size * R + A * R from Nat.add_mul d.size A R]; omega
  have hrB : r ≤ B := chunkCount_le hd hB
  have hrs : r.size ≤ B := (Nat.size_le_self r).trans hrB
  have hms := Nat.size_le_self m
  have hds : d.size ≤ d.size * R := Nat.le_mul_of_pos_right _ hR
  have hR0 : N.size + b.size + σ.size + q.size + B + m + d.size + 1 ≤
      (A + M + d.size + 2) * R := by
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]; omega
  have hmeta : ConcreteSupplier.metadataSpace N b σ q m alphabet limit p d r ≤ H * R :=
    ((selected_metadataSpace_le N b σ q d B hd hB).trans
      (Nat.mul_le_mul_left (100 * (d + 1)) hR0)).trans_eq (by dsimp only [H]; rw [← Nat.mul_assoc])
  have hcontext : (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length ≤ H * R :=
    (context_le_metadataSpace _ _ _ _ _ _ _ _ _ _).trans hmeta
  have hsum : B + m ≤ (A + M) * R := by rw [Nat.add_mul A M R]; omega
  have hpoint : d * r * (2 * p.size + 1) ≤ P * R :=
    ((selected_point_cost_le hd hB).trans (Nat.mul_le_mul_left (17 * d) hsum)).trans_eq
      (by dsimp only [P]; rw [← Nat.mul_assoc])
  have hcell : r * (2 * p.size + 1) ≤ P * R :=
    ((Nat.le_mul_of_pos_left _ hd).trans_eq (Nat.mul_assoc d r _).symm).trans hpoint
  have hlog := Nat.log2_le_size N
  have hsmall : b + Nat.log2 N + cards + 1 ≤ (cards + 3) * R := by
    have hc := Nat.le_mul_of_pos_right cards hR
    have hbN : b + N.size ≤ R := by dsimp only [R]; omega
    rw [Nat.add_mul cards 3 R]; omega
  have hreplay0 := Nat.mul_le_mul_left (1024 * (k + 1)) hsmall
  have hreplay : ConcreteSupplier.replaySpace k s Q N b q m r ≤ replay * R := by
    have hrow := Nat.le_mul_of_pos_right row hR
    simp only [ConcreteSupplier.replaySpace, SupplierChunk.encContext, length_encPair,
      length_encNat_eq_size]
    rw [hrow_eq, Nat.add_assoc (b + N.log2), hcards_eq, show Encoding.width k s b = B from rfl,
      ← Nat.add_assoc _ (2 * (4 * q.size + row + 2) + 2),
      show replay * R = (4 * (M * R) + 3 * (A * R) + 8 * R + 2 * (row * R) + 10 * R) +
        1024 * (k + 1) * ((cards + 3) * R) by
          dsimp only [replay]; rw [Nat.add_mul, Nat.mul_assoc (1024 * (k + 1))]
          simp only [Nat.add_mul, Nat.mul_assoc]]
    refine Nat.add_le_add ?_ hreplay0
    clear hrow_eq hcards_eq hB hreplay0
    clear_value d A M B m r p alphabet limit R replay; omega
  have hreply : ConcreteSupplier.replySpace k s Q N b σ q m alphabet limit p d r ≤ reply * R := by
    simp only [ConcreteSupplier.replySpace, ConcreteSupplier.gateSpace, length_encNat_eq_size]
    rw [Nat.mul_assoc 2 r, show reply * R =
      48 * (H * R + 2 * (P * R) + R) + 16 * (A * R) + 3 * (P * R) + replay * R + 14 * R by
        dsimp only [reply]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, one_mul]]
    omega
  have hmetadataR : (Initializer.encMetadata
      ((Initializer.prepare k s (N, b, σ, q)).1)).length ≤ ci * R :=
    (hci N b σ q).trans (Nat.mul_le_mul_left ci hargs)
  have hinit0 := Initializer.space_prepare_le k s N b σ q
  have hinit1 := Nat.mul_le_mul_left (192 * (d + 1))
    (show 2 * B + d.size ≤ (2 * A + d.size) * R by rw [Nat.add_mul, Nat.mul_assoc]; omega)
  have hinit : Initializer.space k ((Initializer.prepare k s (N, b, σ, q)).1) ≤ init * R := by
    change Initializer.space k ((Initializer.prepare k s (N, b, σ, q)).1) ≤
      16 * ((Initializer.encMetadata ((Initializer.prepare k s (N, b, σ, q)).1)).length + 1) +
        192 * (d + 1) * (2 * B + d.size) at hinit0
    dsimp only [init]
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc 16 ci R, Nat.mul_assoc (192 * _)]
    omega
  have hraw := hcr (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length
    (ConcreteSupplier.replySpace k s Q N b σ q m alphabet limit p d r) b q hb
  change RawController.Query.queryStateBound
    (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length p d r q
    (ConcreteSupplier.replySpace k s Q N b σ q m alphabet limit p d r) ≤
      4 * (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length +
        ConcreteSupplier.replySpace k s Q N b σ q m alphabet limit p d r +
        cr * (b + q * (b.size + 1) + 1) at hraw
  have hraw1 := Nat.mul_le_mul_left cr
    (show b + q * (b.size + 1) + 1 ≤ R by dsimp only [R]; omega)
  change Initializer.space k ((Initializer.prepare k s (N, b, σ, q)).1) +
      RawController.Query.queryStateBound
        (ConcreteSupplier.encContext (N, b, σ, q, m, alphabet, limit)).length p d r q
        (ConcreteSupplier.replySpace k s Q N b σ q m alphabet limit p d r) + 2 ≤
      (init + 4 * H + reply + cr + 2) * R
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_assoc 4 H R]
  omega

/-- The uniform schedule allowance has the fixed-machine square-root-simulation storage shape. -/
theorem scheduleAllowance_le (k s : ℕ) (Q : Type) : ∃ C, ∀ N b q : ℕ, 0 < b →
    InitializedEvaluator.scheduleAllowance k s Q N b q ≤
      C * (b + q * (b.size + 1) + N.size + 1) := by
  obtain ⟨c, hc⟩ := initialized_allowance_le k s Q
  refine ⟨c * (2 * (k + 1) + 2), fun N b q hb => ?_⟩
  have hkq := Nat.mul_le_mul_left (2 * (k + 1))
    (Nat.le_mul_of_pos_right q (by omega : 0 < b.size + 1))
  have hcounter := counter_encoding_le k q (3 ^ ((k + 1) * q)) le_rfl
  rw [length_encNat_eq_size] at hcounter
  have harg : b + q * (b.size + 1) + N.size + (3 ^ ((k + 1) * q)).size + 1 ≤
      (2 * (k + 1) + 2) * (b + q * (b.size + 1) + N.size + 1) := by
    simp only [Nat.add_mul (2 * (k + 1)) 2, Nat.mul_add (2 * (k + 1))]; omega
  exact ((hc N b (3 ^ ((k + 1) * q)) q hb).trans (Nat.mul_le_mul_left c harg)).trans_eq
    (Nat.mul_assoc c _ _).symm

end Turing.MultiTapePTM.BlockComputation.ScheduleSearch
