/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalTerm

/-!
# The one-interval simulation as a term: the replay

`Bounded W N n` bounds every digit of a numeric configuration: the stored tape
numbers below `3^W` and the head indices at most `W`. A step raises `W` by one
(`bounded_nStep`), the start of an interval is bounded with `W = 3b`
(`bounded_nStart`), so for `b` steps every digit fits the radix
`radix b N s = 3^(4b) + N + s + 3`.

`runT` replays the coins (the low `b` bits of a number) by folding `stepT`;
`runT_denote` shows it computes the packed numeric replay.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeNTM.ChoiceTable

variable {w : List Bool} {k s : ℕ} {State : Type} {e : State ≃ Fin s}
  {machine : MultiTapePTM k Bool State}

/-! ### Bounds -/

/-- Every digit bounded, with stored tape numbers below `3^W`. -/
structure Bounded (s W N : ℕ) (n : NCfg k) : Prop where
  st : n.st < s + 1
  tr : n.tr < 3
  ip : n.ip ≤ N + 1
  heads : ∀ h, (n.tapes h).1 < 3
  left : ∀ h, (n.tapes h).2.1 < 3 ^ W
  right : ∀ h, (n.tapes h).2.2 < 3 ^ W
  rho : ∀ h, n.rho h ≤ W

theorem Bounded.wf {W N : ℕ} {n : NCfg k} (h : Bounded s W N n) : WF (s := s) n :=
  ⟨h.st, h.heads⟩

theorem bounded_nStep {W : ℕ} {n : NCfg k} (h : Bounded s W w.length n) (bit : Bool) :
    Bounded s (W + 1) w.length (nStep e machine w n bit) := by
  refine ⟨stc_lt e _, trc_lt _, ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · show moveInputPosNat _ _ _ ≤ _
    rw [moveInputPosNat_eq]; exact min_le_left _ _
  · exact (NTape.step_bound (h.heads h') (h.left h') (h.right h') _).1
  · exact (NTape.step_bound (h.heads h') (h.left h') (h.right h') _).2.1
  · exact (NTape.step_bound (h.heads h') (h.left h') (h.right h') _).2.2
  · show moveNat _ _ ≤ _
    have := h.rho h'
    cases ((machine.coinAction (stOf e n.st) (inputAt w n.ip)
      (fun h => cellOf (n.tapes h).1) bit).workTapes h').2 <;> simp only [moveNat] <;> omega

/-- The radix used for an interval of `b` steps on an input of length `N`. -/
def radix (b N s : ℕ) : ℕ := 3 ^ (4 * b) + N + s + 3

theorem fits_of_bounded {b W N : ℕ} {n : NCfg k} (h : Bounded s W N n) (hW : W ≤ 4 * b) :
    Fits (radix b N s) n := by
  have h3 : 3 ^ W ≤ 3 ^ (4 * b) := Nat.pow_le_pow_right (by norm_num) hW
  have hW' : W < 3 ^ (4 * b) := lt_of_le_of_lt hW (Nat.lt_pow_self (by norm_num))
  intro i hi
  unfold radix
  unfold comp
  split_ifs with h0 h1 h2 hk hf0 hf1 hf2
  · have := h.st; omega
  · have := h.ip; omega
  · have := h.tr; omega
  · have := h.heads ⟨_, hk⟩; omega
  · have := h.left ⟨_, hk⟩; omega
  · have := h.right ⟨_, hk⟩; omega
  · have := h.rho ⟨_, hk⟩; omega
  · omega

/-- The input position of the start is at most `N + 1`. -/
theorem inputPosOfCoord_le (input : List Bool) (p : ℤ) :
    (inputPosOfCoord input p).val ≤ input.length + 1 := by
  have := (inputPosOfCoord input p).isLt; omega

theorem bounded_nStart {b : ℕ} (input : List Bool) (J : Option (Fin k) → ℤ)
    (cIn : ControlData k State) (wIn : Fin k → List (Option Bool))
    (hst : stc e cIn.1 < s + 1) (hoff : ∀ h, cIn.2.1 (some h) < b)
    (hlen : ∀ h, (wIn h).length ≤ 3 * b) :
    Bounded s (3 * b) input.length (nStart e b input J cIn wIn) := by
  refine ⟨hst, trc_lt _, inputPosOfCoord_le _ _, fun h => cc_lt _, fun h => ?_, fun h => ?_,
    fun h => ?_⟩
  · show packDigits 3 _ (b + cIn.2.1 (some h)) < _
    refine lt_of_lt_of_le (packDigits_lt (by norm_num) _ _ fun i _ => cc_lt _)
      (Nat.pow_le_pow_right (by norm_num) ?_)
    have := hoff h; omega
  · show packDigits 3 _ (wIn h).length < _
    exact lt_of_lt_of_le (packDigits_lt (by norm_num) _ _ fun i _ => cc_lt _)
      (Nat.pow_le_pow_right (by norm_num) (hlen h))
  · show b + cIn.2.1 (some h) ≤ 3 * b
    have := hoff h; omega

/-! ### The replay term -/

variable (e machine) in
/-- Replay the low `bT` bits of `x` as coins from the packed configuration `start`. -/
def runT (R N bT x start : Term) : Term :=
  foldT bT start fun acc j => stepT e machine R N acc (bit x j)

/-- The replay of the first `j` coins of `x`. -/
def runPrefix (input : List Bool) (x j : ℕ) (n : NCfg k) : NCfg k :=
  (List.range j).foldl (fun n i => nStep e machine input n (x.testBit i)) n

theorem nRun_coinsOf (input : List Bool) (b x : ℕ) (n : NCfg k) :
    nRun e machine input (coinsOf b x) n = runPrefix (e := e) (machine := machine) input x b n := by
  unfold nRun coinsOf runPrefix
  rw [List.foldl_map]

theorem bounded_runPrefix {W : ℕ} {n : NCfg k} (h : Bounded s W w.length n) (x : ℕ) :
    ∀ j, Bounded s (W + j) w.length (runPrefix (e := e) (machine := machine) w x j n) := by
  intro j
  induction j with
  | zero => simpa [runPrefix] using h
  | succ j ih =>
    unfold runPrefix
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact bounded_nStep ih _

/-- **The replay term computes the packed numeric replay** of the low `b` bits. -/
theorem runT_denote (R N bT x start : Term) (env : List ℕ) (hR : StableAt w R env)
    (hN : StableAt w N env) (hx : StableAt w x env)
    {b : ℕ} (hRv : R.denote w env = radix b w.length s) (hNv : N.denote w env = w.length)
    (hbv : bT.denote w env = b) {n : NCfg k} (hn : Bounded s (3 * b) w.length n)
    (hstart : start.denote w env = cpack (radix b w.length s) n) :
    (runT e machine R N bT x start).denote w env =
      cpack (radix b w.length s) (nRun e machine w (coinsOf b (x.denote w env)) n) := by
  rw [nRun_coinsOf, runT, denote_foldT, hbv, hstart]
  have hpos : 0 < radix b w.length s := by unfold radix; positivity
  suffices ∀ j ≤ b, foldAcc w (fun acc j => stepT e machine R N acc (bit x j)) env
      (cpack (radix b w.length s) n) j =
      cpack (radix b w.length s) (runPrefix (e := e) (machine := machine) w (x.denote w env) j n)
    from this b le_rfl
  intro j
  induction j with
  | zero => intro _; simp [runPrefix]
  | succ j ih =>
    intro hj
    rw [foldAcc_succ, ih (by omega)]
    have hb := bounded_runPrefix (e := e) (machine := machine) hn (x.denote w env) j
    set acc := cpack (radix b w.length s)
      (runPrefix (e := e) (machine := machine) w (x.denote w env) j n)
    have hR' : StableAt w R (acc :: j :: env) := hR.extend [acc, j]
    have hN' : StableAt w N (acc :: j :: env) := hN.extend [acc, j]
    have hx' : StableAt w x (acc :: j :: env) := hx.extend [acc, j]
    rw [stepT_denote R N (lvl (env.length + 1)) (bit x (lvl env.length)) (acc :: j :: env)
      hR' hN' (stableAt_lvl (by simp))
      (StableAt.bit hx' (stableAt_lvl (by simp)))
      (by rw [hR.cons₂]; exact hRv) hpos (by rw [hN.cons₂]; exact hNv)
      (fits_of_bounded hb (by omega)) hb.wf (by simp [acc])
      (b := (x.denote w env).testBit j) (by simp [hx.cons₂])]
    unfold runPrefix
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end Cslib.Complexity.NtimeDspace.LocalSim
