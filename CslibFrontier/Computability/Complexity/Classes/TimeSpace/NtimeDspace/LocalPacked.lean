/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalRun

/-!
# The one-interval simulation in codes

The numeric step `nStep` decodes its numbers to call the machine. Here the
step is restated on codes only (`nStepC`): the machine is consulted through
finite tables of the key (state, input cell, coin, work head cells), and every
other operation is arithmetic. `nStep_eq_nStepC` holds on well-formed
configurations. Configurations are packed in one number with a fixed radix
(`pack`), and `nStepC` preserves the bounds that make the radix work for `b`
steps (`Good`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeNTM.ChoiceTable

variable {k s : ℕ} {State : Type} (e : State ≃ Fin s) (machine : MultiTapePTM k Bool State)

/-! ### Codes of actions -/

def sgnCode : SignType → ℕ
  | .neg => 0
  | .zero => 1
  | .pos => 2

def wCode : Option (Option Bool) → ℕ
  | none => 0
  | some c => cc c + 1

/-- The number of keys. -/
def keyCount (k s : ℕ) : ℕ := (s + 1) * (3 * (2 * 3 ^ k))

/-- The key of a state code, an input cell code, a coin and the work head cells
(as base-3 digits `wk`). -/
def keyOf (s st inc bit wk : ℕ) : ℕ := st + (s + 1) * (inc + 3 * (bit + 2 * wk))

/-- The action of a key. -/
def actOf (key : ℕ) : Turing.Action k Bool State :=
  machine.coinAction (stOf e (key % (s + 1))) (cellOf (key / (s + 1) % 3))
    (fun h => cellOf (key / (s + 1) / 3 / 2 / 3 ^ (h : ℕ) % 3)) (key / (s + 1) / 3 % 2 = 1)

/-- The head cells of a configuration as base-3 digits. -/
def headsOf (tapes : Fin k → NTape) : ℕ :=
  packDigits 3 (fun i => if h : i < k then (tapes ⟨i, h⟩).1 else 0) k

theorem headsOf_digit {tapes : Fin k → NTape} (ht : ∀ h, (tapes h).1 < 3) (h : Fin k) :
    headsOf tapes / 3 ^ (h : ℕ) % 3 = (tapes h).1 := by
  unfold headsOf
  rw [packDigits_div_pow_mod (by norm_num) _ _ (fun i hi => by rw [dif_pos hi]; exact ht _),
    if_pos h.isLt, dif_pos h.isLt]

theorem headsOf_lt (tapes : Fin k → NTape) (ht : ∀ h, (tapes h).1 < 3) :
    headsOf tapes < 3 ^ k :=
  packDigits_lt (by norm_num) _ _ fun i hi => by rw [dif_pos hi]; exact ht _

variable {e machine} in
theorem actOf_keyOf {st inc bit : ℕ} {tapes : Fin k → NTape} (hst : st < s + 1) (hinc : inc < 3)
    (hbit : bit < 2) (ht : ∀ h, (tapes h).1 < 3) :
    actOf e machine (keyOf s st inc bit (headsOf tapes)) =
      machine.coinAction (stOf e st) (cellOf inc) (fun h => cellOf (tapes h).1) (bit = 1) := by
  unfold actOf keyOf
  have h1 : (st + (s + 1) * (inc + 3 * (bit + 2 * headsOf tapes))) % (s + 1) = st := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hst]
  have h2 : (st + (s + 1) * (inc + 3 * (bit + 2 * headsOf tapes))) / (s + 1) =
      inc + 3 * (bit + 2 * headsOf tapes) := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hst, zero_add]
  have h3 : (inc + 3 * (bit + 2 * headsOf tapes)) / 3 = bit + 2 * headsOf tapes := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hinc, zero_add]
  have h4 : (bit + 2 * headsOf tapes) / 2 = headsOf tapes := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hbit, zero_add]
  rw [h1, h2, h3, h4]
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hinc, Nat.mod_eq_of_lt hbit,
    headsOf_digit ht]

theorem keyOf_lt {st inc bit wk : ℕ} (hst : st < s + 1) (hinc : inc < 3) (hbit : bit < 2)
    (hwk : wk < 3 ^ k) : keyOf s st inc bit wk < keyCount k s := by
  unfold keyOf keyCount
  have : inc + 3 * (bit + 2 * wk) < 3 * (2 * 3 ^ k) := by omega
  nlinarith

/-! ### The machine as tables -/

def fSt (key : ℕ) : ℕ := stc e (actOf e machine key).state
def fIn (key : ℕ) : ℕ := sgnCode (actOf e machine key).inputTape
def fOut (key : ℕ) : ℕ := cc (actOf e machine key).output

/-- The write code of tape `x / keyCount` at key `x % keyCount`. -/
def fW (x : ℕ) : ℕ :=
  if h : x / keyCount k s < k then
    wCode ((actOf e machine (x % keyCount k s)).workTapes ⟨x / keyCount k s, h⟩).1
  else 0

/-- The move code of tape `x / keyCount` at key `x % keyCount`. -/
def fM (x : ℕ) : ℕ :=
  if h : x / keyCount k s < k then
    sgnCode ((actOf e machine (x % keyCount k s)).workTapes ⟨x / keyCount k s, h⟩).2
  else 0

/-- The track code after emitting the cell with code `x / 3` on the track with code `x % 3`. -/
def fEmit (x : ℕ) : ℕ := trc ((trOf (x % 3)).emit (cellOf (x / 3)))

theorem fW_key {key : ℕ} (hkey : key < keyCount k s) (h : Fin k) :
    fW e machine (key + keyCount k s * h) = wCode ((actOf e machine key).workTapes h).1 := by
  have hK : 0 < keyCount k s := by unfold keyCount; positivity
  have hd : (key + keyCount k s * h) / keyCount k s = h := by
    rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hkey, zero_add]
  have hm : (key + keyCount k s * h) % keyCount k s = key := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hkey]
  unfold fW
  rw [dif_pos (by rw [hd]; exact h.isLt)]
  simp only [hm, hd]

theorem fM_key {key : ℕ} (hkey : key < keyCount k s) (h : Fin k) :
    fM e machine (key + keyCount k s * h) = sgnCode ((actOf e machine key).workTapes h).2 := by
  have hK : 0 < keyCount k s := by unfold keyCount; positivity
  have hd : (key + keyCount k s * h) / keyCount k s = h := by
    rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hkey, zero_add]
  have hm : (key + keyCount k s * h) % keyCount k s = key := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hkey]
  unfold fM
  rw [dif_pos (by rw [hd]; exact h.isLt)]
  simp only [hm, hd]

/-! ### The step in codes -/

def moveC (r m : ℕ) : ℕ := if m = 0 then r - 1 else if m = 1 then r else r + 1

def ipC (n ip m : ℕ) : ℕ := min (n + 1) (moveC ip m)

def tapeC (t : NTape) (wc mc : ℕ) : NTape :=
  let hd := if wc = 0 then t.1 else wc - 1
  if mc = 0 then (t.2.1 % 3, t.2.1 / 3, t.2.2 * 3 + hd)
  else if mc = 1 then (hd, t.2.1, t.2.2)
  else (t.2.2 % 3, t.2.1 * 3 + hd, t.2.2 / 3)

theorem moveNat_eq (r : ℕ) (m : SignType) : moveNat r m = moveC r (sgnCode m) := by
  cases m <;> rfl

theorem moveInputPosNat_eq (n ip : ℕ) (m : SignType) :
    moveInputPosNat n ip m = ipC n ip (sgnCode m) := by
  unfold moveInputPosNat ipC moveC
  cases m <;> simp [sgnCode, SignType.cast] <;> omega

theorem tapeC_eq (t : NTape) (a : Option (Option Bool) × SignType) :
    t.step a = tapeC t (wCode a.1) (sgnCode a.2) := by
  rcases a with ⟨w, m⟩
  cases w <;> cases m <;> simp [NTape.step, tapeC, wCode, sgnCode, NTape.write, NTape.moveLeft,
    NTape.moveRight]

/-- The key of a configuration and a coin. -/
def keyAt (input : List Bool) (n : NCfg k) (bit : Bool) : ℕ :=
  keyOf s n.st (cc (inputAt input n.ip)) bit.toNat (headsOf n.tapes)

/-- **One coin step in codes.** -/
def nStepC (input : List Bool) (n : NCfg k) (bit : Bool) : NCfg k :=
  let key := keyAt (s := s) input n bit
  { st := fSt e machine key
    ip := ipC input.length n.ip (fIn e machine key)
    tapes := fun h => tapeC (n.tapes h) (fW e machine (key + keyCount k s * h))
      (fM e machine (key + keyCount k s * h))
    rho := fun h => moveC (n.rho h) (fM e machine (key + keyCount k s * h))
    tr := fEmit (n.tr % 3 + 3 * fOut e machine key) }

/-- Well-formed codes. -/
structure WF (n : NCfg k) : Prop where
  st : n.st < s + 1
  heads : ∀ h, (n.tapes h).1 < 3

variable {e machine}

theorem keyAt_lt {input : List Bool} {n : NCfg k} (hn : WF (s := s) n) (bit : Bool) :
    keyAt (s := s) input n bit < keyCount k s :=
  keyOf_lt hn.st (cc_lt _) (by cases bit <;> simp) (headsOf_lt _ hn.heads)

theorem actOf_keyAt {input : List Bool} {n : NCfg k} (hn : WF (s := s) n) (bit : Bool) :
    actOf e machine (keyAt (s := s) input n bit) =
      machine.coinAction (stOf e n.st) (inputAt input n.ip) (fun h => cellOf (n.tapes h).1)
          bit := by
  unfold keyAt
  rw [actOf_keyOf hn.st (cc_lt _) (by cases bit <;> simp) hn.heads, cellOf_cc]
  cases bit <;> rfl

/-- **The code step is the numeric step** on well-formed configurations. -/
theorem nStep_eq_nStepC {input : List Bool} {n : NCfg k} (hn : WF (s := s) n) (bit : Bool) :
    nStep e machine input n bit = nStepC e machine input n bit := by
  have hk := keyAt_lt (s := s) (input := input) hn bit
  have ha := actOf_keyAt (e := e) (machine := machine) (input := input) hn bit
  unfold nStep nStepC
  simp only [fSt, fIn, fOut, fW_key e machine hk, fM_key e machine hk, ha]
  congr 1
  · exact moveInputPosNat_eq _ _ _
  · funext h; exact tapeC_eq _ _
  · funext h; exact moveNat_eq _ _
  · unfold fEmit trOf
    congr 2
    · simp [Nat.add_mul_mod_self_left]
    · rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (Nat.mod_lt _ (by norm_num)),
        zero_add, cellOf_cc]

theorem NTape.step_head_lt {t : NTape} (h1 : t.1 < 3) (a : Option (Option Bool) × SignType) :
    (t.step a).1 < 3 := by
  rcases a with ⟨w, m⟩
  cases w <;> cases m <;>
    simp [NTape.step, NTape.write, NTape.moveLeft, NTape.moveRight, h1, cc_lt, Nat.mod_lt]

theorem wf_nStep {input : List Bool} {n : NCfg k} (hn : WF (s := s) n) (bit : Bool) :
    WF (s := s) (nStep e machine input n bit) :=
  ⟨stc_lt e _, fun h => NTape.step_head_lt (hn.heads h) _⟩

end Cslib.Complexity.NtimeDspace.LocalSim
