/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Step
import Mathlib.Tactic.FinCases

/-!
# Simulating a step

A configuration of the Hennie–Stearns machine represents a configuration `c` of `tm` (`Rep`)
when its work tape `0` holds tracks representing the work tapes of `c`, its work tape `1` is
clean, and its input head and output are those of `c`. The machine starts in a representation of
the initial configuration (`rep_init`), takes a represented step in time
`1 + ∑ 80 · 2 ^ j` (`rep_step`), and halts with the output of `tm` (`step_halt`).
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

variable {k : ℕ} {Symbol State : Type} {x : List Symbol}

/-! ### Reading the input -/

lemma inputSymbol_hcfg {st : Option (HState k State)} {p : Fin ((x.map Sum.inl).length + 2)}
    {A B : ℤ → Option (HSym k Symbol)} {pA pB : ℤ} {out : List (HSym k Symbol)}
    {c : Cfg k Symbol State x} (hp : p.val = c.inputPos.val) :
    (hcfg st p A B pA pB out).inputSymbol = c.inputSymbol.map Sum.inl := by
  have hl : (x.map (Sum.inl (β := ACell k Symbol ⊕ BCell Symbol))).length = x.length :=
    List.length_map _
  have hlt := c.inputPos.isLt
  have hpos : (hcfg st p A B pA pB out).inputPos = p := rfl
  by_cases hb : c.inputPos.val = 0 ∨ c.inputPos.val = x.length + 1
  · rw [inputSymbol_eq_none_of_boundary (cfg := c) hb,
      inputSymbol_eq_none_of_boundary (cfg := hcfg st p A B pA pB out)
        (by rw [hpos, hp, hl]; exact hb)]
    rfl
  · rw [inputSymbolInner (cfg := c) (c.inputPos.val - 1) (by omega) (by omega),
      inputSymbolInner (cfg := hcfg st p A B pA pB out) (c.inputPos.val - 1)
        (by rw [hpos, hp]; omega) (by rw [hl]; omega)]
    simp

lemma readIn_map (v : Option Symbol) : readIn (k := k) (v.map Sum.inl) = v := by
  cases v <;> rfl

lemma val_moveInputPos_map
    {p : Fin ((x.map (Sum.inl (β := ACell k Symbol ⊕ BCell Symbol))).length + 2)}
    {c : Cfg k Symbol State x}
    (hp : p.val = c.inputPos.val) (m : SignType) :
    (moveInputPos p m).val = (moveInputPos c.inputPos m).val := by
  have h₁ := val_moveInputPos_eq p m
  have h₂ := val_moveInputPos_eq c.inputPos m
  have hl : (x.map (Sum.inl (β := ACell k Symbol ⊕ BCell Symbol))).length = x.length :=
    List.length_map _
  have hl' : ((x.map (Sum.inl (β := ACell k Symbol ⊕ BCell Symbol))).length : ℤ) = x.length := by
    exact_mod_cast hl
  have hp' : ((p.val : ℕ) : ℤ) = ((c.inputPos.val : ℕ) : ℤ) := by exact_mod_cast hp
  omega

/-! ### Reading and writing the centers -/

/-- The new symbol under the head of track `i` after the action `a`. -/
def newCenter (a : Action k Symbol State) (Z : Fin k → ZTrack Symbol) (i : Fin k) :
    Option Symbol :=
  match (a.workTapes i).1 with
  | none => (Z i).center
  | some v => v

/-- The tracks after writing the centers. -/
def written (a : Action k Symbol State) (Z : Fin k → ZTrack Symbol) (i : Fin k) : ZTrack Symbol :=
  (Z i).withCenter (newCenter a Z i)

lemma update_encA_center (a : Action k Symbol State) (Z : Fin k → ZTrack Symbol) (J : ℕ) :
    Function.update (encA Z J none) 0
        (some (.inr (.inl { centerCell Z with r := fun i => match (a.workTapes i).1 with
          | none => (centerCell Z).r i
          | some v => some v }))) =
      encA (written a Z) J none := by
  funext z
  by_cases hz : z = 0
  · subst hz
    rw [Function.update_self]
    simp only [encA, le_refl, ↓reduceIte, Int.toNat_zero, aCell, Option.map_some, centerCell,
      written, newCenter]
    have : (fun i => match (a.workTapes i).1 with
        | none => some (Z i).center
        | some v => some v) = fun i => some ((Z i).withCenter (match (a.workTapes i).1 with
          | none => (Z i).center
          | some v => v)).center := by
      funext i
      rcases (a.workTapes i).1 <;> rfl
    rw [this]
  · rw [Function.update_of_ne hz]
    simp only [encA, aCell]
    split_ifs <;> first | rfl | omega

variable (tm : MultiTapeTM k Symbol State)

/-- The action of `tm` in state `q` on the input symbol `v` and the centers of `Z`. -/
noncomputable abbrev actOf (q : State) (v : Option Symbol) (Z : Fin k → ZTrack Symbol) :
    Action k Symbol State :=
  tm.tr q v fun i => (Z i).center

/-- The moves of the heads. -/
def moves (a : Action k Symbol State) (i : Fin k) : SignType := (a.workTapes i).2

/-- **Reading and writing the centers.** -/
lemma step_apply (q : State) {input : List (HSym k Symbol)} (p : Fin (input.length + 2))
    (Z : Fin k → ZTrack Symbol) (J : ℕ) (out : List (HSym k Symbol)) :
    (hennieStearns tm).step (hcfg (some (.apply q)) p (encA Z J none) (encB [] []) 0 1 out) =
      hcfg (((actOf tm q (readIn (hcfg (some (.apply q)) p (encA Z J none) (encB [] []) 0 1
          out).inputSymbol) Z).state).map fun q' =>
          startOp q' (moves (actOf tm q (readIn (hcfg (some (.apply q)) p (encA Z J none)
            (encB [] []) 0 1 out).inputSymbol) Z)) 0)
        (moveInputPos p (actOf tm q (readIn (hcfg (some (.apply q)) p (encA Z J none)
          (encB [] []) 0 1 out).inputSymbol) Z).inputTape)
        (encA (written (actOf tm q (readIn (hcfg (some (.apply q)) p (encA Z J none)
          (encB [] []) 0 1 out).inputSymbol) Z) Z) J none) (encB [] []) 0 1
        (out ++ ((actOf tm q (readIn (hcfg (some (.apply q)) p (encA Z J none) (encB [] []) 0 1
          out).inputSymbol) Z).output.map Sum.inl).toList) := by
  rw [step_hcfg]
  generalize (hcfg (some (HState.apply q)) p (encA Z J none) (encB [] []) 0 1 out).inputSymbol = v
  have h0 : readA (![encA Z J none 0, encB (k := k) [] [] 1] 0) = some (centerCell Z) :=
    readA_encA_zero Z J none
  simp only [hsTr, h0]
  have ha : tm.tr q (readIn v) (fun i => ((centerCell Z).r i).getD none) =
      actOf tm q (readIn v) Z := rfl
  rw [ha]
  generalize actOf tm q (readIn v) Z = a
  refine Cfg.ext ?_ rfl ?_ ?_ rfl
  · simp only [Action.apply, hcfg, startOp]
    rcases a.state <;> rfl
  · funext j
    fin_cases j
    · simp only [Action.apply, hcfg]
      exact update_encA_center a Z J
    · rfl
  · funext j
    fin_cases j <;> simp [Action.apply, hcfg]

/-! ### The representation -/

/-- The configuration `h` of the Hennie–Stearns machine represents the running configuration `c`
of `tm`, with tracks `Z` and `J` levels. -/
structure Rep (c : Cfg k Symbol State x) (Z : Fin k → ZTrack Symbol) (J : ℕ)
    (h : Cfg 2 (HSym k Symbol) (HState k State) (x.map Sum.inl)) : Prop where
  valid : ∀ i, (Z i).Valid J
  agree : ∀ i, (Z i).Agree J (c.workTapes i) (c.workTapePos i)
  pos : h.inputPos.val = c.inputPos.val
  eq : h = hcfg (c.state.map .apply) h.inputPos (encA Z J none) (encB [] []) 0 1
    (c.output.map Sum.inl)

lemma ZTrack.Agree.congr {Y : ZTrack Symbol} {J J' : ℕ} {t : ℤ → Option Symbol} {p : ℤ}
    (h : Y.Agree J t p) (hV : Y.Valid J) (hV' : Y.Valid J') : Y.Agree J' t p := by
  rcases le_total J J' with hJ | hJ
  · exact h.mono hV hJ
  · refine ⟨h.1, fun m => ?_⟩
    rw [← ZTrack.decode_mono hV' hJ, ← ZTrack.decode_mono hV' hJ]
    exact h.2 m

lemma actOf_rep {c : Cfg k Symbol State x} {Z : Fin k → ZTrack Symbol} {J : ℕ}
    {h : Cfg 2 (HSym k Symbol) (HState k State) (x.map Sum.inl)} (hR : Rep c Z J h) (q : State) :
    actOf tm q (readIn (hcfg (some (HState.apply q)) h.inputPos (encA Z J none)
      (encB [] []) 0 1 (c.output.map Sum.inl)).inputSymbol) Z =
      tm.tr q c.inputSymbol c.workTapeSymbols := by
  rw [inputSymbol_hcfg hR.pos, readIn_map]
  simp only [actOf]
  congr 1
  funext i
  exact (hR.agree i).1

/-- **A represented step.** -/
theorem rep_step {c : Cfg k Symbol State x} {Z : Fin k → ZTrack Symbol} {J : ℕ}
    {h : Cfg 2 (HSym k Symbol) (HState k State) (x.map Sum.inl)} (hR : Rep c Z J h) {q : State}
    (hq : c.state = some q) (hq' : (tm.step c).state ≠ none) :
    ∃ T J', T ≤ 1 + opsTime (moves (tm.tr q c.inputSymbol c.workTapeSymbols)) 0
        (written (tm.tr q c.inputSymbol c.workTapeSymbols) Z) J ∧
      Rep (tm.step c) (movedFrom (moves (tm.tr q c.inputSymbol c.workTapeSymbols)) 0
        (written (tm.tr q c.inputSymbol c.workTapeSymbols) Z) J) J'
        ((hennieStearns tm).runFrom h T) := by
  set a := tm.tr q c.inputSymbol c.workTapeSymbols with hadef
  set mv := moves a
  set W := written a Z
  have hstep : tm.step c = a.apply c := step_of_state hq
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.1 hq'
  have haq : a.state = some q' := by rw [← hq', hstep]; rfl
  have hact := actOf_rep tm hR q
  have hVW : ∀ i, (W i).Valid J := fun i => (hR.valid i).withCenter _
  obtain ⟨T, J', hT, hJ', hV', hrun⟩ := runFrom_ops tm q' mv
    (moveInputPos h.inputPos a.inputTape) ((c.output.map Sum.inl) ++ (a.output.map Sum.inl).toList)
    0 W J hVW
  have hfinal : (hennieStearns tm).runFrom h (1 + T) =
      hcfg (some (.apply q')) (moveInputPos h.inputPos a.inputTape)
        (encA (movedFrom mv 0 W J) J' none) (encB [] []) 0 1
        (c.output.map Sum.inl ++ (a.output.map Sum.inl).toList) := by
    rw [runFrom_add, runFrom_one]
    conv_lhs => rw [hR.eq]
    rw [hq, Option.map_some, step_apply, hact, haq, Option.map_some]
    exact hrun
  refine ⟨1 + T, J', by omega, ⟨hV', fun i => ?_, ?_, ?_⟩⟩
  · -- the work tapes
    have hW : (W i).Agree J ((tm.step c).workTapes i) (c.workTapePos i) := by
      rw [hstep]
      simp only [Action.apply, W, written, newCenter]
      rcases (a.workTapes i).1 with _ | v
      · exact hR.agree i
      · exact (hR.agree i).write v
    have hpos : (tm.step c).workTapePos i = c.workTapePos i + mv i := by rw [hstep]; rfl
    rw [hpos]
    simp only [movedFrom, zero_le, true_and]
    have hVi := hV' i
    rw [movedFrom] at hVi
    split_ifs with hm
    · rw [ite_eq_left (show 0 ≤ i.val ∧ mv i ≠ 0 from ⟨Nat.zero_le _, hm⟩)] at hVi
      exact (hW.move (hVW i) hm).congr ((hVW i).move _) hVi
    · rw [ite_eq_right (show ¬ (0 ≤ i.val ∧ mv i ≠ 0) from fun h' => hm h'.2)] at hVi
      rw [show mv i = 0 by simpa using hm, SignType.coe_zero, add_zero]
      exact hW.congr (hVW i) hVi
  · rw [hfinal, hstep]
    exact val_moveInputPos_map hR.pos _
  · rw [hfinal, hq', Option.map_some, hstep]
    congr 1
    simp only [Action.apply, List.map_append]
    rcases a.output <;> rfl

/-- **The halting step.** -/
theorem step_halt {c : Cfg k Symbol State x} {Z : Fin k → ZTrack Symbol} {J : ℕ}
    {h : Cfg 2 (HSym k Symbol) (HState k State) (x.map Sum.inl)} (hR : Rep c Z J h) {q : State}
    (hq : c.state = some q) (hhalt : (tm.step c).state = none) :
    ((hennieStearns tm).runFrom h 1).state = none ∧
      ((hennieStearns tm).runFrom h 1).output = (tm.step c).output.map Sum.inl := by
  have hstep : tm.step c = (tm.tr q c.inputSymbol c.workTapeSymbols).apply c := step_of_state hq
  have haq : (tm.tr q c.inputSymbol c.workTapeSymbols).state = none := by
    rw [← hhalt, hstep]; rfl
  have hh : h = hcfg (some (.apply q)) h.inputPos (encA Z J none) (encB [] []) 0 1
      (c.output.map Sum.inl) := by
    have := hR.eq
    rwa [hq, Option.map_some] at this
  have e := step_apply tm q h.inputPos Z J (c.output.map Sum.inl)
  rw [actOf_rep tm hR q, haq] at e
  rw [runFrom_one, hh, e, hstep]
  refine ⟨rfl, ?_⟩
  simp only [hcfg, Action.apply, List.map_append]
  rcases (tm.tr q c.inputSymbol c.workTapeSymbols).output <;> rfl

/-! ### The start -/

/-- The track of a blank tape. -/
def blankTrack : ZTrack Symbol := ⟨none, fun _ j => List.replicate (2 ^ j) none⟩

lemma blankTrack_valid : (blankTrack (Symbol := Symbol)).Valid 0 :=
  ⟨fun _ _ => by simp [blankTrack], fun j => by simp [blankTrack, pow_succ]; omega,
    fun _ _ _ => rfl⟩

lemma blankTrack_balanced : (blankTrack (Symbol := Symbol)).Balanced := fun _ _ => by
  simp [blankTrack]

lemma initCfg_hennieStearns :
    (hennieStearns tm).initCfg (x.map Sum.inl) =
      hcfg (some .init) 1 (fun _ => none) (fun _ => none) 0 0 [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> rfl

/-- **The start.** After one step, the machine represents the initial configuration of `tm`. -/
theorem rep_init (x : List Symbol) :
    Rep (tm.initCfg x) (fun _ => blankTrack) 0
      ((hennieStearns tm).runFrom ((hennieStearns tm).initCfg (x.map Sum.inl)) 1) := by
  have hrun : (hennieStearns tm).runFrom ((hennieStearns tm).initCfg (x.map Sum.inl)) 1 =
      hcfg (some (.apply tm.q₀)) 1 (encA (fun _ => blankTrack) 0 none) (encB [] []) 0 1 [] := by
    rw [runFrom_one, initCfg_hennieStearns, step_hcfg]
    simp only [hsTr, act_apply, Option.elim_some]
    congr 1
    · funext z
      by_cases hz : z = 0
      · subst hz; simp [encA, aCell, centerCell, initCenter, blankTrack]
      · rw [Function.update_of_ne hz]
        simp only [encA, aCell]
        split_ifs <;> first | rfl | omega
    · funext z
      by_cases hz : z = 0
      · subst hz; rfl
      · rw [Function.update_of_ne hz]
        simp only [encB, hz, ↓reduceIte]
        split_ifs <;> rfl
  refine ⟨fun _ => blankTrack_valid, fun i => ⟨rfl, fun m => ⟨rfl, rfl⟩⟩, ?_, ?_⟩
  · rw [hrun]; rfl
  · rw [hrun]; rfl

end Turing.MultiTapeTM.HennieStearns
