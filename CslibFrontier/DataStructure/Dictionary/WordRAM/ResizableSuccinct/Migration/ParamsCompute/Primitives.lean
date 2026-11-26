/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shared Low-Level `Memory.Prog` Combinators, Bounded `log₂` Loop, and Block Writers

Internal primitive evaluators, `Fits` offset helpers, bounded floor-`log₂` iteration
(`log2CapProg`), saturating/min/max/zero-branch combinators, and 3/4/8-word contiguous block writers
shared across the `ParamsCompute` submodules.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ParamsComputeAux

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Word-Width `Fits` and Ceiling-Logarithm Helpers -/

/-- Any word width accommodating `225` satisfies `8 ≤ w`. -/
theorem eight_le_of_fits_225 {w : ℕ} (h225 : Fits w 225) : 8 ≤ w := by
  by_contra! hlt8
  exact absurd (h225.trans_le (Nat.pow_le_pow_right two_pos (Nat.lt_succ_iff.mp hlt8))) (by decide)

/-- Whenever `Fits w 225`, `3 * w + 5` also fits in `w` bits. -/
theorem fits_three_mul_w_add_five {w : ℕ} (h225 : Fits w 225) : Fits w (3 * w + 5) := by
  unfold Fits
  refine Nat.le_induction (by decide) (fun k _ ih => ?_) w (eight_le_of_fits_225 h225)
  rw [pow_succ']
  omega

/-- Any header offset `dstMetaBase + k` with `k ≤ 225` fits in `w` bits when
`dstMetaBase + offCompItems U w N` fits. -/
theorem fits_add_of_fits_offCompItems {w U N dstMetaBase k : ℕ}
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) (hk : k ≤ 225) :
    Fits w (dstMetaBase + k) :=
  hfit_dst.of_le (by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega)

/-- The end of the hash-table region `(dstMetaBase + epochHdrWords) + epochHashSpace U w N` fits
in `w` bits when `dstMetaBase + offCompItems U w N` fits. -/
theorem fits_hash_of_fits_offCompItems {w U N dstMetaBase : ℕ}
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    Fits w ((dstMetaBase + epochHdrWords) + epochHashSpace U w N) :=
  hfit_dst.of_le (by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM; omega)

/-- Exact ceiling-to-floor binary logarithm identity `⌈log₂ x⌉ = ⌊log₂ (x - 1)⌋ + 1` for `1 < x`. -/
theorem clog2_eq_log2_pred_add_one {x : ℕ} (hx : 1 < x) :
    Nat.clog 2 x = Nat.log 2 (x - 1) + 1 := by
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow one_lt_two]
    have hlt := Nat.lt_pow_succ_log_self one_lt_two (x - 1)
    omega
  · have hle_c := Nat.le_pow_clog one_lt_two x
    refine (Nat.log_lt_iff_lt_pow one_lt_two (by omega)).mpr ?_
    omega

/-- Shifted ceiling-to-floor binary logarithm identity `⌈log₂ (m + 1)⌉ = ⌊log₂ m⌋ + 1` for
`1 ≤ m`. -/
theorem clog2_succ_eq_log2_add_one {m : ℕ} (hm : 1 ≤ m) :
    Nat.clog 2 (m + 1) = Nat.log 2 m + 1 := by
  rw [clog2_eq_log2_pred_add_one (by omega), Nat.add_sub_cancel]

/-! ## Bounded Floor-`log₂` Loop (`log2CapProg`) -/

private def log2CapAux : ℕ → ℕ → ℕ × ℕ
  | 0, rem => (rem, 0)
  | k + 1, rem =>
    if 1 < rem then
      let p := log2CapAux k (rem / 2)
      (p.1, p.2 + 1)
    else (rem, 0)

private theorem log2CapAux_snd (k rem : ℕ) : (log2CapAux k rem).2 = min k (Nat.log 2 rem) := by
  induction k generalizing rem with
  | zero => simp [log2CapAux]
  | succ k ih =>
    dsimp only [log2CapAux]
    split_ifs with h1
    · rw [ih (rem / 2), Nat.log_of_one_lt_of_le one_lt_two h1]
      omega
    · simp [Nat.log_of_lt (by omega : rem < 2)]

private theorem log2CapAux_step (k rem acc : ℕ) :
    let next := if 1 < rem then (rem / 2, acc + 1) else (rem, acc)
    next.2 + (log2CapAux k next.1).2 = acc + (log2CapAux (k + 1) rem).2 := by
  dsimp only [log2CapAux]
  split_ifs with h1
  · dsimp only; omega
  · have h0 : (log2CapAux k rem).2 = 0 := by
      rw [log2CapAux_snd, Nat.log_of_lt (by omega), Nat.min_zero]
    dsimp only; omega

private def log2StepProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (hdrAddr, (rem, acc)) => do
    let _ ← Memory.read hdrAddr
    if 1 < rem then pure (rem >>> 1, acc + 1) else pure (rem, acc)

private theorem clientState_log2StepProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (log2StepProg x) = s := by
  rcases x with ⟨hdrAddr, ⟨rem, acc⟩⟩
  dsimp only [log2StepProg]
  rw [StateTransitionSpec.clientState_bind]
  have hs0 : (Memory.spec 0).clientState s (Memory.read hdrAddr) = s := rfl
  rw [hs0]
  split_ifs <;> rfl

private theorem validHistory_log2StepProg {w hdrAddr rem acc : ℕ} {s : Memory.State}
    (hfr : hdrAddr < s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (log2StepProg (hdrAddr, (rem, acc)))) := by
  dsimp only [log2StepProg]
  rw [validHistory_bind']; refine ⟨⟨hfr, trivial⟩, ?_⟩
  simp only [StateTransitionSpec.clientState, prog_runClient_state_read]
  split_ifs <;> trivial

private def Log2StepPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (hdrAddr, (rem, acc)), s =>
    hdrAddr < s.frontier ∧ Fits w rem ∧ Fits w (acc + 1)

private theorem realizesBounded_log2Step :
    RealizesBounded .exact log2StepProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ × ℕ))
      Log2StepPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨hdrAddr, ⟨rem, acc⟩⟩
    obtain ⟨hfr, hrem, hacc1⟩ := h
    try dsimp only at *)
  all_goals try omega
  all_goals exact hacc1.of_le (by omega)

private theorem memoryCost_log2Step_ge_one (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (log2StepProg x) s := by
  rcases x with ⟨hdrAddr, ⟨rem, acc⟩⟩
  dsimp only [log2StepProg]
  rw [Realization.memoryCost_bind', prog_memoryCost_read]
  split_ifs <;> omega

private theorem memoryCost_log2Step_le_one (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (log2StepProg x) s ≤ 1 := by
  rcases x with ⟨hdrAddr, ⟨rem, acc⟩⟩
  dsimp only [log2StepProg]
  simp only [Realization.memoryCost_bind', prog_memoryCost_read, StateTransitionSpec.clientState,
    prog_runClient_state_read]
  split_ifs <;> exact le_rfl

private theorem log2Loop_spec {w hdrAddr K x₀ : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hx₀ : Fits w x₀) (hK : Fits w (min K (Nat.log 2 x₀) + 1)) :
    let prog := iterate log2StepProg hdrAddr K (x₀, 0)
    iterationSafe log2StepProg Log2StepPre w hdrAddr K (x₀, 0) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ K ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    ((Memory.spec 0).clientResult s₀ prog).2 = min K (Nat.log 2 x₀) := by
  intro prog
  let inv (k : ℕ) (st : ℕ × ℕ) (s : Memory.State) : Prop :=
    s = s₀ ∧ st.1 ≤ x₀ ∧ st.2 + (log2CapAux (K - k) st.1).2 = (log2CapAux K x₀).2 ∧
    st.2 ≤ min K (Nat.log 2 x₀)
  obtain ⟨hsafe, hv, hcost, _, _, hs_eq, _, hsum_end, _⟩ :=
    iterate_spec log2StepProg Log2StepPre w hdrAddr 1 K inv (fun _ => False)
      (fun k hk st s ⟨hs_eq, hle_x, hsum, hacc_le⟩ => by
        subst hs_eq
        rcases st with ⟨rem, acc⟩
        change rem ≤ x₀ at hle_x
        change acc + (log2CapAux (K - k) rem).2 = (log2CapAux K x₀).2 at hsum
        change acc ≤ min K (Nat.log 2 x₀) at hacc_le
        have hrem_fit : Fits w rem := hx₀.of_le hle_x
        have hacc1_fit : Fits w (acc + 1) := hK.of_le (by omega)
        have hs' := clientState_log2StepProg (hdrAddr, (rem, acc)) s
        have hres : (Memory.spec 0).clientResult s (log2StepProg (hdrAddr, (rem, acc))) =
            if 1 < rem then (rem / 2, acc + 1) else (rem, acc) := by
          dsimp only [log2StepProg]
          simp only [prog_clientResult_bind, StateTransitionSpec.clientState,
            prog_runClient_state_read]
          split_ifs <;> simp only [prog_clientResult_pure, Nat.shiftRight_eq_div_pow, pow_one]
        refine ⟨⟨hfr, hrem_fit, hacc1_fit⟩, validHistory_log2StepProg hfr,
          memoryCost_log2Step_le_one _ _,
          congrArg Memory.State.frontier hs',
          (fun _ _ => by rw [hs']),
          hs', ?_⟩
        have hst := log2CapAux_step (K - (k + 1)) rem acc
        dsimp only at hst
        rw [show K - (k + 1) + 1 = K - k by omega] at hst
        rw [hres]
        split_ifs at hst ⊢ with h1 <;> dsimp only at hst ⊢
        · have hpos : 1 ≤ (log2CapAux (K - k) rem).2 := by
            rw [log2CapAux_snd]
            exact le_min (by omega) (Nat.le_log_of_pow_le one_lt_two (by omega))
          have := log2CapAux_snd K x₀
          exact ⟨(Nat.div_le_self _ _).trans hle_x, hst.trans hsum, by omega⟩
        · exact ⟨hle_x, hst.trans hsum, hacc_le⟩)
      (x₀, 0) s₀ ⟨rfl, le_rfl, by simp, Nat.zero_le _⟩
  refine ⟨hsafe, hv, by simpa only [one_mul] using hcost, hs_eq, ?_⟩
  simp only [Nat.sub_self, log2CapAux, Nat.add_zero] at hsum_end
  exact hsum_end.trans (log2CapAux_snd K x₀)

/-- Bounded `K`-step evaluator computing `min K (Nat.log 2 x₀)` via `iterate`. -/
def log2CapProg : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (hdrAddr, (K, x₀)) => do
    let (_, res) ← iterate log2StepProg hdrAddr K (x₀, 0)
    pure res

/-- Precondition for `log2CapProg`. -/
@[expose] def Log2CapPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (hdrAddr, (K, x₀)), s =>
    hdrAddr < s.frontier ∧ Fits w x₀ ∧ Fits w (min K (Nat.log 2 x₀) + 1)

/-- `log2CapProg` compiles via `RealizesBounded .exact`. -/
theorem realizesBounded_log2Cap :
    RealizesBounded .exact log2CapProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      Log2CapPre (fun _ _ => 0) := by
  have hlg := RealizesBounded.iterate₀ (WordEncoding.encode (α := ℕ))
    (WordEncoding.encode (α := ℕ × ℕ)) realizesBounded_log2Step memoryCost_log2Step_ge_one
  realize
  rcases d with ⟨hdrAddr, ⟨K, x₀⟩⟩
  obtain ⟨hfr, hx₀, hK⟩ := h
  exact (log2Loop_spec hfr hx₀ hK).1

/-- Functional specification and `≤ K` cost bound for `log2CapProg`. -/
theorem log2CapProg_spec {w hdrAddr K x₀ : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hx₀ : Fits w x₀) (hK : Fits w (min K (Nat.log 2 x₀) + 1)) :
    let prog := log2CapProg (hdrAddr, (K, x₀))
    Log2CapPre w (hdrAddr, (K, x₀)) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ K ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    (Memory.spec 0).clientResult s₀ prog = min K (Nat.log 2 x₀) := by
  intro prog
  obtain ⟨_, hv, hc, hst, hres⟩ := log2Loop_spec hfr hx₀ hK
  dsimp only [prog, log2CapProg]
  rw [validHistory_bind', Realization.memoryCost_bind', StateTransitionSpec.clientState_bind,
    prog_clientResult_bind, hst]
  rcases hp : (Memory.spec 0).clientResult s₀ (iterate log2StepProg hdrAddr K (x₀, 0)) with ⟨_, r⟩
  rw [hp] at hres
  exact ⟨⟨hfr, hx₀, hK⟩, ⟨hv, trivial⟩, by dsimp only; rw [memoryCost_pure]; omega, rfl, hres⟩

/-! ## Pure Scalar Combinators and Read/Write Step Helpers -/

/-- `ValidHistory` step lemma for a single `Memory.read`. -/
theorem validHistory_read_step {α : Type} {w a fr : ℕ} {mem : ℕ → ℕ}
    {k : ℕ → Memory.Prog α} (ha : a < fr)
    (hk : (Memory.spec w).ValidHistory { mem := mem, frontier := fr }
      ((Memory.spec w).clientHistory { mem := mem, frontier := fr } (k (mem a)))) :
    (Memory.spec w).ValidHistory { mem := mem, frontier := fr }
      ((Memory.spec w).clientHistory { mem := mem, frontier := fr } (Memory.read a >>= k)) :=
  ⟨ha, hk⟩

/-- `ValidHistory` step lemma for a single `Memory.write`. -/
theorem validHistory_write_step {α : Type} {w a v fr : ℕ} {mem : ℕ → ℕ}
    {k : Unit → Memory.Prog α} (ha : a < fr) (hv : Fits w v)
    (hk : (Memory.spec w).ValidHistory { mem := Function.update mem a v, frontier := fr }
      ((Memory.spec w).clientHistory { mem := Function.update mem a v, frontier := fr }
        (k ()))) :
    (Memory.spec w).ValidHistory { mem := mem, frontier := fr }
      ((Memory.spec w).clientHistory { mem := mem, frontier := fr } (Memory.write a v >>= k)) :=
  ⟨⟨ha, hv⟩, hk⟩

/-- Saturating natural subtraction `a - b` in `Memory.Prog` without underflow. -/
def subSatProg : ℕ × ℕ → Memory.Prog ℕ
  | (a, b) => if a < b then pure 0 else pure (a - b)

@[simp] theorem clientResult_subSatProg (a b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (subSatProg (a, b)) = a - b := by
  dsimp only [subSatProg]
  split_ifs with h
  · simp only [prog_clientResult_pure]; omega
  · simp only [prog_clientResult_pure]

theorem clientState_subSatProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (subSatProg p) = s := by
  rcases p with ⟨a, b⟩; dsimp only [subSatProg]; split_ifs <;> rfl

@[simp] theorem runClient_snd_subSatProg (p : ℕ × ℕ) (s : Memory.State) :
    Prod.snd ((Memory.spec 0).runClient s (subSatProg p)) = (s, []) := by
  rcases p with ⟨a, b⟩; dsimp only [subSatProg]; split_ifs <;> rfl

@[simp] theorem memoryCost_subSatProg (p : ℕ × ℕ) (s : Memory.State) :
    memoryCost (subSatProg p) s = 0 := by
  rcases p with ⟨a, b⟩; dsimp only [subSatProg]; split_ifs <;> rfl

theorem validHistory_subSatProg {w : ℕ} (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (subSatProg p)) := by
  rcases p with ⟨a, b⟩; dsimp only [subSatProg]; split_ifs <;> trivial

theorem realizesBounded_subSat :
    RealizesBounded .exact subSatProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  rcases d with ⟨a, b⟩
  dsimp only at *
  omega

/-- Minimum `min a b` in `Memory.Prog`. -/
def minNatProg : ℕ × ℕ → Memory.Prog ℕ
  | (a, b) => if a < b then pure a else pure b

@[simp] theorem clientResult_minNatProg (a b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (minNatProg (a, b)) = min a b := by
  dsimp only [minNatProg]
  split_ifs with h <;> simp only [prog_clientResult_pure]
  · exact (Nat.min_eq_left h.le).symm
  · exact (Nat.min_eq_right (Nat.le_of_not_lt h)).symm

theorem clientState_minNatProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (minNatProg p) = s := by
  rcases p with ⟨a, b⟩; dsimp only [minNatProg]; split_ifs <;> rfl

@[simp] theorem runClient_snd_minNatProg (p : ℕ × ℕ) (s : Memory.State) :
    Prod.snd ((Memory.spec 0).runClient s (minNatProg p)) = (s, []) := by
  rcases p with ⟨a, b⟩; dsimp only [minNatProg]; split_ifs <;> rfl

@[simp] theorem memoryCost_minNatProg (p : ℕ × ℕ) (s : Memory.State) :
    memoryCost (minNatProg p) s = 0 := by
  rcases p with ⟨a, b⟩; dsimp only [minNatProg]; split_ifs <;> rfl

theorem validHistory_minNatProg {w : ℕ} (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (minNatProg p)) := by
  rcases p with ⟨a, b⟩; dsimp only [minNatProg]; split_ifs <;> trivial

theorem realizesBounded_minNat :
    RealizesBounded .exact minNatProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Maximum `max a b` in `Memory.Prog`. -/
def maxNatProg : ℕ × ℕ → Memory.Prog ℕ
  | (a, b) => if a < b then pure b else pure a

@[simp] theorem clientResult_maxNatProg (a b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (maxNatProg (a, b)) = max a b := by
  dsimp only [maxNatProg]
  split_ifs with h <;> simp only [prog_clientResult_pure]
  · exact (Nat.max_eq_right h.le).symm
  · exact (Nat.max_eq_left (Nat.le_of_not_lt h)).symm

theorem clientState_maxNatProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (maxNatProg p) = s := by
  rcases p with ⟨a, b⟩; dsimp only [maxNatProg]; split_ifs <;> rfl

@[simp] theorem runClient_snd_maxNatProg (p : ℕ × ℕ) (s : Memory.State) :
    Prod.snd ((Memory.spec 0).runClient s (maxNatProg p)) = (s, []) := by
  rcases p with ⟨a, b⟩; dsimp only [maxNatProg]; split_ifs <;> rfl

@[simp] theorem memoryCost_maxNatProg (p : ℕ × ℕ) (s : Memory.State) :
    memoryCost (maxNatProg p) s = 0 := by
  rcases p with ⟨a, b⟩; dsimp only [maxNatProg]; split_ifs <;> rfl

theorem validHistory_maxNatProg {w : ℕ} (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (maxNatProg p)) := by
  rcases p with ⟨a, b⟩; dsimp only [maxNatProg]; split_ifs <;> trivial

theorem realizesBounded_maxNat :
    RealizesBounded .exact maxNatProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Zero-comparison conditional `if x = 0 then tVal else fVal` in `Memory.Prog`. -/
def ifEqZeroProg : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (x, (tVal, fVal)) => do
    let z0 ← pure 0
    if x = z0 then pure tVal else pure fVal

@[simp] theorem clientResult_ifEqZeroProg (x tVal fVal : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (ifEqZeroProg (x, (tVal, fVal))) =
      if x = 0 then tVal else fVal := by
  dsimp only [ifEqZeroProg]; simp only [pure_bind]
  split_ifs <;> simp only [prog_clientResult_pure]

theorem clientState_ifEqZeroProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (ifEqZeroProg p) = s := by
  rcases p with ⟨x, ⟨tVal, fVal⟩⟩; dsimp only [ifEqZeroProg]; simp only [pure_bind]
  split_ifs <;> rfl

@[simp] theorem runClient_snd_ifEqZeroProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    Prod.snd ((Memory.spec 0).runClient s (ifEqZeroProg p)) = (s, []) := by
  rcases p with ⟨x, ⟨tVal, fVal⟩⟩; dsimp only [ifEqZeroProg]; simp only [pure_bind]
  split_ifs <;> rfl

@[simp] theorem memoryCost_ifEqZeroProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (ifEqZeroProg p) s = 0 := by
  rcases p with ⟨x, ⟨tVal, fVal⟩⟩; dsimp only [ifEqZeroProg]; simp only [pure_bind]
  split_ifs <;> rfl

theorem validHistory_ifEqZeroProg {w : ℕ} (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ifEqZeroProg p)) := by
  rcases p with ⟨x, ⟨tVal, fVal⟩⟩; dsimp only [ifEqZeroProg]; simp only [pure_bind]
  split_ifs <;> trivial

theorem realizesBounded_ifEqZero :
    RealizesBounded .exact ifEqZeroProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-! ## Contiguous 3-, 4-, and 8-Word Block Writers -/

/-- Write 3 contiguous words `(v0, (v1, v2))` at `[base, base + 3)`. -/
@[expose] def writeBlock3Prog : ℕ × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (base, (v0, (v1, v2))) => do
    Memory.write base v0
    Memory.write (base + 1) v1
    Memory.write (base + 2) v2

/-- Precondition for `writeBlock3Prog`. -/
@[expose] def WriteBlock3Pre (w : ℕ) : ℕ × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | (base, _), s => base + 3 ≤ s.frontier ∧ Fits w (base + 2)

theorem realizesBounded_writeBlock3 :
    RealizesBounded .exact writeBlock3Prog
      (WordEncoding.encode (α := ℕ × (ℕ × (ℕ × ℕ)))) (WordEncoding.encode (α := Unit))
      WriteBlock3Pre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨base, ⟨v0, ⟨v1, v2⟩⟩⟩
    obtain ⟨_hfr, hbase2⟩ := h
    dsimp only at *)
  all_goals exact hbase2.of_le (by omega)

theorem writeBlock3Prog_spec {w : ℕ} (base v0 v1 v2 : ℕ) {s : Memory.State}
    (hfr : base + 3 ≤ s.frontier) (hfit_end : Fits w (base + 2))
    (hv0 : Fits w v0) (hv1 : Fits w v1) (hv2 : Fits w v2) :
    let d : ℕ × (ℕ × (ℕ × ℕ)) := (base, (v0, (v1, v2)))
    let prog := writeBlock3Prog d
    let s' := (Memory.spec 0).clientState s prog
    WriteBlock3Pre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (s'.mem base = v0 ∧ s'.mem (base + 1) = v1 ∧ s'.mem (base + 2) = v2) ∧
    (∀ a, ¬(base ≤ a ∧ a < base + 3) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 3 := by
  intro d prog s'
  refine ⟨⟨hfr, hfit_end⟩, ?_, ?_⟩
  · rcases s with ⟨mem, fr⟩
    dsimp only [prog, d, writeBlock3Prog] at hfr ⊢
    refine validHistory_write_step (by omega) hv0 ?_
    refine validHistory_write_step (by omega) hv1 ?_
    exact ⟨⟨show base + 2 < fr by omega, hv2⟩, trivial⟩
  · dsimp only [s', prog, d, writeBlock3Prog, StateTransitionSpec.clientState]
    simp (disch := omega) only [prog_runClient_state_bind, prog_runClient_state_write,
      Realization.memoryCost_bind', prog_memoryCost_write, Function.update_of_ne,
      Function.update_self, true_and, and_true]
    intro a ha
    simp (disch := omega) only [Function.update_of_ne]

/-- Write 4 contiguous words `((v0, v1), (v2, v3))` at `[base, base + 4)`. -/
@[expose] def writeBlock4Prog : ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (base, ((v0, v1), (v2, v3))) => do
    Memory.write base v0
    Memory.write (base + 1) v1
    Memory.write (base + 2) v2
    Memory.write (base + 3) v3

/-- Precondition for `writeBlock4Prog`. -/
@[expose] def WriteBlock4Pre (w : ℕ) : ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (base, _), s => base + 4 ≤ s.frontier ∧ Fits w (base + 3)

theorem realizesBounded_writeBlock4 :
    RealizesBounded .exact writeBlock4Prog
      (WordEncoding.encode (α := ℕ × ((ℕ × ℕ) × (ℕ × ℕ)))) (WordEncoding.encode (α := Unit))
      WriteBlock4Pre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨base, ⟨⟨v0, v1⟩, ⟨v2, v3⟩⟩⟩
    obtain ⟨_hfr, hbase3⟩ := h
    dsimp only at *)
  all_goals exact hbase3.of_le (by omega)

theorem writeBlock4Prog_spec {w : ℕ} (base v0 v1 v2 v3 : ℕ) {s : Memory.State}
    (hfr : base + 4 ≤ s.frontier) (hfit_end : Fits w (base + 3))
    (hv0 : Fits w v0) (hv1 : Fits w v1) (hv2 : Fits w v2) (hv3 : Fits w v3) :
    let d : ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) := (base, ((v0, v1), (v2, v3)))
    let prog := writeBlock4Prog d
    let s' := (Memory.spec 0).clientState s prog
    WriteBlock4Pre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (s'.mem base = v0 ∧ s'.mem (base + 1) = v1 ∧ s'.mem (base + 2) = v2 ∧
      s'.mem (base + 3) = v3) ∧
    (∀ a, ¬(base ≤ a ∧ a < base + 4) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 4 := by
  intro d prog s'
  refine ⟨⟨hfr, hfit_end⟩, ?_, ?_⟩
  · rcases s with ⟨mem, fr⟩
    dsimp only [prog, d, writeBlock4Prog] at hfr ⊢
    refine validHistory_write_step (by omega) hv0 ?_
    refine validHistory_write_step (by omega) hv1 ?_
    refine validHistory_write_step (by omega) hv2 ?_
    exact ⟨⟨show base + 3 < fr by omega, hv3⟩, trivial⟩
  · dsimp only [s', prog, d, writeBlock4Prog, StateTransitionSpec.clientState]
    simp (disch := omega) only [prog_runClient_state_bind, prog_runClient_state_write,
      Realization.memoryCost_bind', prog_memoryCost_write, Function.update_of_ne,
      Function.update_self, true_and, and_true]
    intro a ha
    simp (disch := omega) only [Function.update_of_ne]

/-- Specification for two consecutive `writeBlock4Prog` calls writing slice `[off, off + 8)` of
`g : Fin n → ℕ` into `[base, base + 8)`. -/
theorem writeTwoBlock4Fin_spec {w n : ℕ} (base : ℕ) (g : Fin n → ℕ) (off : ℕ)
    (hoff : off + 8 ≤ n) {s : Memory.State}
    (hfr : base + 8 ≤ s.frontier) (hfit_end : Fits w (base + 7))
    (hg : ∀ i : Fin n, Fits w (g i)) :
    let b0 := ((g ⟨off, by omega⟩, g ⟨off + 1, by omega⟩),
      (g ⟨off + 2, by omega⟩, g ⟨off + 3, by omega⟩))
    let b1 := ((g ⟨off + 4, by omega⟩, g ⟨off + 5, by omega⟩),
      (g ⟨off + 6, by omega⟩, g ⟨off + 7, by omega⟩))
    let prog := writeBlock4Prog (base, b0) >>= fun _ => writeBlock4Prog (base + 4, b1)
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8), s'.mem (base + j) = g ⟨off + j, by omega⟩) ∧
    (∀ a, ¬(base ≤ a ∧ a < base + 8) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 8 := by
  intro b0 b1 prog s'
  obtain ⟨_, hv0, hfr0, hm0, hframe0, hc0⟩ :=
    writeBlock4Prog_spec base (g ⟨off, by omega⟩) (g ⟨off + 1, by omega⟩)
      (g ⟨off + 2, by omega⟩) (g ⟨off + 3, by omega⟩) (s := s)
      (by omega) (hfit_end.of_le (by omega)) (hg _) (hg _) (hg _) (hg _)
  set s1 := (Memory.spec 0).clientState s (writeBlock4Prog (base, b0))
  obtain ⟨_, hv1, hfr1, hm1, hframe1, hc1⟩ :=
    writeBlock4Prog_spec (base + 4) (g ⟨off + 4, by omega⟩) (g ⟨off + 5, by omega⟩)
      (g ⟨off + 6, by omega⟩) (g ⟨off + 7, by omega⟩) (s := s1)
      (by omega) (hfit_end.of_le (by omega)) (hg _) (hg _) (hg _) (hg _)
  have hs'_eq : s' = (Memory.spec 0).clientState s1 (writeBlock4Prog (base + 4, b1)) :=
    StateTransitionSpec.clientState_bind ..
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog]; rw [validHistory_bind']; exact ⟨hv0, hv1⟩
  · rw [hs'_eq, hfr1, hfr0]
  · intro j hj
    rw [hs'_eq]
    obtain ⟨m00, m01, m02, m03⟩ := hm0
    obtain ⟨m10, m11, m12, m13⟩ := hm1
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact m10 | exact m11 | exact m12 | exact m13
      | (rw [hframe1 _ (by omega)]; first | exact m00 | exact m01 | exact m02 | exact m03)
  · intro a ha
    rw [hs'_eq, hframe1 a (by omega), hframe0 a (by omega)]
  · dsimp only [prog]; rw [Realization.memoryCost_bind', hc0, hc1]

/-- Specification for two consecutive `writeBlock4Prog` calls followed by `pure ret`. -/
theorem writeTwoBlock4FinRet_spec {w n : ℕ} (base : ℕ) (g : Fin n → ℕ) (off : ℕ)
    (hoff : off + 8 ≤ n) (ret : ℕ) {s : Memory.State}
    (hfr : base + 8 ≤ s.frontier) (hfit_end : Fits w (base + 7))
    (hg : ∀ i : Fin n, Fits w (g i)) :
    let b0 := ((g ⟨off, by omega⟩, g ⟨off + 1, by omega⟩),
      (g ⟨off + 2, by omega⟩, g ⟨off + 3, by omega⟩))
    let b1 := ((g ⟨off + 4, by omega⟩, g ⟨off + 5, by omega⟩),
      (g ⟨off + 6, by omega⟩, g ⟨off + 7, by omega⟩))
    let prog := writeBlock4Prog (base, b0) >>= fun _ =>
      writeBlock4Prog (base + 4, b1) >>= fun _ => pure ret
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = ret ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8), s'.mem (base + j) = g ⟨off + j, by omega⟩) ∧
    (∀ a, ¬(base ≤ a ∧ a < base + 8) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 8 := by
  intro b0 b1 prog s'
  obtain ⟨hv, hfr', hmem', hframe', hc⟩ :=
    writeTwoBlock4Fin_spec base g off hoff hfr hfit_end hg
  have hbind : prog =
      (writeBlock4Prog (base, b0) >>= fun _ => writeBlock4Prog (base + 4, b1)) >>=
        fun _ => pure ret := bind_assoc ..
  have hs'_eq : s' = (Memory.spec 0).clientState s
      (writeBlock4Prog (base, b0) >>= fun _ => writeBlock4Prog (base + 4, b1)) := by
    dsimp only [s']; rw [hbind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbind, validHistory_bind']; exact ⟨hv, trivial⟩
  · rw [hbind, prog_clientResult_bind, prog_clientResult_pure]
  · rw [hs'_eq]; exact hfr'
  · intro j hj; rw [hs'_eq]; exact hmem' j hj
  · intro a ha; rw [hs'_eq]; exact hframe' a ha
  · rw [hbind, Realization.memoryCost_bind', memoryCost_pure, hc]

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ParamsComputeAux
