/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.TM2.SingleTapeSpace
public import CslibFrontier.Computability.Machines.Turing.SingleTape.TM0WindowEncoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial finite windows for standard PSPACE machines

Bounded native head-coordinate paths lift to finite windows of the same width. Initial and
canonical halting windows pad the standard compiler's tapes by blanks.

## Main definitions

* `Turing.TM2Computable.inputWindow`: the original input padded to polynomial width.
* `Turing.TM2Computable.haltWindow`: the canonical Boolean halt configuration at the same width.

## Main results

* `Turing.TM0Window.headRange_reaches`: a native head-range path executes inside its finite window.
* `Turing.TM2Computable.computableInPolyTime_inputWindow`: the actual padded input constructor.
* `Turing.TM2Computable.computableInPolyTime_haltWindow`: the canonical Boolean target constructor.
* `Cslib.Complexity.mem_PSPACE_exists_windowTM0`: standard PSPACE acceptance in these windows.
-/

public section

attribute [local instance] Turing.FinTM2.ΛFin

namespace Turing.TM0Window

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {Γ Q : Type*} [Inhabited Γ]

section

variable [Inhabited Q]

private def Tracks (lo hi : ℤ) (c : Cfg Γ Q) (x : HeadPosition.Cfg Γ Q) : Prop :=
  c.toNative = x.native ∧ (c.left.length : ℤ) = x.position - lo ∧
    (c.right.length : ℤ) = hi - x.position

private theorem tracks_step {M : TM0.Machine Γ Q} {lo hi : ℤ} {c : Cfg Γ Q}
    {x y : HeadPosition.Cfg Γ Q} (hc : Tracks lo hi c x)
    (hs : HeadPosition.StepWithin M lo hi x y) :
    ∃ d, step M c = some d ∧ Tracks lo hi d y := by
  rcases c with ⟨q, a, L, R⟩
  rcases x with ⟨native, p⟩
  obtain ⟨he, hL, hR⟩ := hc
  have hn : native = TM0.cfgOf q a L R := he.symm
  subst native
  cases hM : M q a with
  | none => simp only [HeadPosition.StepWithin, HeadPosition.step, TM0.cfgOf, hM,
      Option.map_none] at hs; cases hs.1
  | some result =>
    rcases result with ⟨q', action⟩
    cases action with
    | write b =>
      have hy : y = ⟨TM0.cfgOf q' b L R, p⟩ := by
        apply Option.some.inj
        simpa only [HeadPosition.step, TM0.cfgOf, hM, Option.map_some, Tape.write] using hs.1.symm
      subst y
      exact ⟨⟨q', b, L, R⟩, by simp only [step, hM], rfl, hL, hR⟩
    | move direction =>
      cases direction with
      | left =>
        have hy : y = ⟨TM0.cfgOf q' L.headI L.tail (a :: R), p - 1⟩ := by
          apply Option.some.inj
          simpa only [HeadPosition.step, TM0.cfgOf, hM, Option.map_some, Tape.move,
            ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk] using hs.1.symm
        subst y
        have hp : lo ≤ p - 1 := hs.2.2.2.1
        have hlen : 0 < L.length := by change (L.length : ℤ) = p - lo at hL; omega
        cases L with
        | nil => cases hlen
        | cons b L =>
          refine ⟨⟨q', b, L, a :: R⟩, by simp only [step, hM], rfl, ?_, ?_⟩ <;>
            simp only [List.length_cons, Int.natCast_succ] at hL hR ⊢ <;> omega
      | right =>
        have hy : y = ⟨TM0.cfgOf q' R.headI (a :: L) R.tail, p + 1⟩ := by
          apply Option.some.inj
          simpa only [HeadPosition.step, TM0.cfgOf, hM, Option.map_some, Tape.move,
            ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk] using hs.1.symm
        subst y
        have hp : p + 1 ≤ hi := hs.2.2.2.2
        have hlen : 0 < R.length := by change (R.length : ℤ) = hi - p at hR; omega
        cases R with
        | nil => cases hlen
        | cons b R =>
          refine ⟨⟨q', b, a :: L, R⟩, by simp only [step, hM], rfl, ?_, ?_⟩ <;>
            simp only [List.length_cons, Int.natCast_succ] at hL hR ⊢ <;> omega

/-- A bounded native head-coordinate path executes inside any matching finite window. -/
theorem headRange_reaches {M : TM0.Machine Γ Q} {lo hi : ℤ}
    {x y : HeadPosition.Cfg Γ Q} (hr : HeadPosition.ReachesWithin M lo hi x y)
    (c : Cfg Γ Q) (hc : c.toNative = x.native)
    (hL : (c.left.length : ℤ) = x.position - lo)
    (hR : (c.right.length : ℤ) = hi - x.position) :
    ∃ d : Cfg Γ Q, StateTransition.Reaches (step M) c d ∧ d.toNative = y.native ∧
      (d.left.length : ℤ) = y.position - lo ∧ (d.right.length : ℤ) = hi - y.position := by
  have htrack : Tracks lo hi c x := ⟨hc, hL, hR⟩
  induction hr with
  | refl => exact ⟨c, .refl, htrack⟩
  | tail _ hs ih =>
    obtain ⟨b, hb, htrack⟩ := ih
    obtain ⟨d, hbd, hd⟩ := tracks_step htrack hs
    exact ⟨d, hb.tail hbd, hd⟩

/-- A native terminal configuration also terminates in every finite window. -/
private theorem step_eq_none_of_native {M : TM0.Machine Γ Q} {c : Cfg Γ Q}
    (h : TM0.step M c.toNative = none) : step M c = none := by
  cases hs : step M c with
  | none => rfl
  | some d =>
    have hn := step_native hs
    rw [h] at hn
    cases hn

end

private theorem mk_injective_of_length {L R : List Γ} (hlen : L.length = R.length)
    (h : ListBlank.mk L = ListBlank.mk R) : L = R := by
  have hrel : BlankRel L R := Quotient.exact' h
  rcases hrel with ⟨n, he⟩ | ⟨n, he⟩
  · have hn : n = 0 := by
      have := congrArg List.length he
      simp only [List.length_append, List.length_replicate] at this
      omega
    simpa only [hn, List.replicate_zero, List.append_nil] using he.symm
  · have hn : n = 0 := by
      have := congrArg List.length he
      simp only [List.length_append, List.length_replicate] at this
      omega
    simpa only [hn, List.replicate_zero, List.append_nil] using he

private theorem toNative_injective_of_lengths {c d : Cfg Γ Q}
    (hL : c.left.length = d.left.length) (hR : c.right.length = d.right.length)
    (h : c.toNative = d.toNative) : c = d := by
  rcases c with ⟨q, a, L, R⟩
  rcases d with ⟨q', a', L', R'⟩
  simp only [Cfg.toNative, TM0.cfgOf, TM0.Cfg.mk.injEq, Tape.mk.injEq] at h
  obtain ⟨rfl, rfl, hl, hr⟩ := h
  have heL : L = L' := mk_injective_of_length hL hl
  have heR : R = R' := mk_injective_of_length hR hr
  subst L'
  subst R'
  rfl

private theorem mk_pad (L : List Γ) (n : ℕ) :
    ListBlank.mk (L ++ List.replicate n default) = ListBlank.mk L :=
  Quotient.sound' (Or.inr ⟨n, rfl⟩)

/-- A tape list placed at the original head position, with one blank cell to the left and
enough blank padding on the right to fill the requested radius. -/
@[expose] def Cfg.ofList (q : Q) (input : List Γ) (radius : ℕ) : Cfg Γ Q :=
  ⟨q, input.headI, [default],
    input.tail ++ List.replicate (radius - input.tail.length) default⟩

/-- Padding the represented interval leaves the native tape unchanged. -/
theorem ofList_toNative (q : Q) (input : List Γ) (radius : ℕ) :
    (Cfg.ofList q input radius).toNative = TM0.cfgOf q input.headI [] input.tail := by
  have hL : ListBlank.mk [default] = ListBlank.mk ([] : List Γ) := mk_pad [] 1
  simp only [Cfg.ofList, Cfg.toNative, TM0.cfgOf, mk_pad, hL]

/-- Every filled origin window has the requested number of cells. -/
theorem ofList_size (q : Q) (input : List Γ) (radius : ℕ) (h : input.tail.length ≤ radius) :
    (Cfg.ofList q input radius).size = radius + 2 := by
  simp only [Cfg.ofList, Cfg.size, List.length_cons, List.length_nil, List.length_append,
    List.length_replicate]
  omega

private theorem ofList_right_length (q : Q) (input : List Γ) (radius : ℕ)
    (h : input.tail.length ≤ radius) : (Cfg.ofList q input radius).right.length = radius := by
  simp only [Cfg.ofList, List.length_append, List.length_replicate]
  omega

/-- A head-range path between filled origin windows is an actual finite-window computation. -/
private theorem reaches_of_headRange [Inhabited Q] {M : TM0.Machine Γ Q}
    {radius : ℕ} {c d : Cfg Γ Q}
    (hr : HeadPosition.ReachesWithin M (-1) radius ⟨c.toNative, 0⟩ ⟨d.toNative, 0⟩)
    (hcL : c.left.length = 1) (hcR : c.right.length = radius)
    (hdL : d.left.length = 1) (hdR : d.right.length = radius) :
    StateTransition.Reaches (step M) c d := by
  obtain ⟨e, hce, he, hL, hR⟩ := headRange_reaches hr c rfl (by simp only [hcL]; omega)
    (by simp only [hcR]; omega)
  have heL : e.left.length = d.left.length := by
    change (e.left.length : ℤ) = 0 - -1 at hL
    omega
  have heR : e.right.length = d.right.length := by
    change (e.right.length : ℤ) = (radius : ℤ) - 0 at hR
    omega
  have hed : e = d := toNative_injective_of_lengths heL heR he
  exact hed ▸ hce

/-- Filling an origin window is polynomial-time in its control, tape list and unary radius. -/
theorem computableInPolyTime_ofList {Γ Q α : Type} [Inhabited Γ] {encIn : α ↪ List Bool}
    [Finite Γ] [Finite Q] {q : α → Q} {input : α → List Γ} {radius : α → ℕ}
    (hq : Turing.MultiTapeTM.ComputableInPolyTime q encIn (Turing.MultiTapeTM.encFinite Q))
    (hi : Turing.MultiTapeTM.ComputableInPolyTime input encIn
      (Turing.MultiTapeTM.encList (Turing.MultiTapeTM.encFinite Γ)))
    (hr : Turing.MultiTapeTM.ComputableInPolyTime radius encIn Turing.MultiTapeTM.encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun a => Cfg.ofList (q a) (input a) (radius a))
      encIn (encCfg (Γ := Γ) (Q := Q)) := by
  have hs : ComputableInPolyTime (fun a => (input a).headI) encIn (encFinite Γ) := by
    convert listHeadDWithInput hi (const default) using 1
    funext a
    cases input a <;> rfl
  have ht := (listTail (encFinite Γ)).comp hi
  have hn := (length_list (encFinite Γ)).comp ht
  have hpad := replicate (encA := encFinite Γ) (unary_sub' hr hn) (const (default : Γ))
  have hright := (listAppend (encFinite Γ)).comp (ht.prod hpad)
  exact encCfg_mk_polyTime hq hs (Turing.MultiTapeTM.ComputableInPolyTime.const [default]) hright

end Turing.TM0Window

namespace Turing.FinTM2

/-- Right radius of the complete finite tape window, including the original binary input. -/
@[expose] def windowRadius (tm : FinTM2) (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  n + p.eval n + TM2to1.headOverhead tm.m + 1

/-- The polynomial window radius can be computed from the unary input length. -/
private theorem computableInPolyTime_windowRadius (tm : FinTM2) (p : Polynomial ℕ) :
    MultiTapeTM.ComputableInPolyTime (tm.windowRadius p) MultiTapeTM.encUnary
      MultiTapeTM.encUnary := by
  change MultiTapeTM.ComputableInPolyTime
    (fun n => n + p.eval n + TM2to1.headOverhead tm.m + 1) _ _
  exact MultiTapeTM.ComputableInPolyTime.unary_add'
    (MultiTapeTM.ComputableInPolyTime.unary_add'
      (MultiTapeTM.ComputableInPolyTime.unary_add' .id' (.unary_eval p))
      (.const (TM2to1.headOverhead tm.m))) (.const 1)

end Turing.FinTM2

namespace Turing.TM2Computable

open Turing.TM0Window Turing.MultiTapeTM

open Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {encIn : α ↪ List Bool} {f : α → Bool}

/-- Finite initial tape, with a blank at coordinate `-1` and polynomial right padding. -/
@[expose] noncomputable def inputWindow (h : TM2Computable encIn encBool f)
    (p : Polynomial ℕ) (a : α) :
    Turing.TM0Window.Cfg (TM2to1.Γ' h.tm.K h.tm.Γ) (FinTM2.TM0Control h.tm) :=
  Turing.TM0Window.Cfg.ofList default
    (TM2to1.trInit h.tm.k₀ (List.map h.inputAlphabet.symm (encIn a)))
    (h.tm.windowRadius p (encIn a).length)

/-- Canonical Boolean halt window at the same width as the input window. -/
@[expose] noncomputable def haltWindow (h : TM2Computable encIn encBool f)
    (p : Polynomial ℕ) (a : α) (bit : Bool) :
    Turing.TM0Window.Cfg (TM2to1.Γ' h.tm.K h.tm.Γ) (FinTM2.TM0Control h.tm) :=
  Turing.TM0Window.Cfg.ofList (h.tm.toTM0Halt [h.outputAlphabet.symm bit]).q
    (TM2to1.trInit h.tm.k₁ [h.outputAlphabet.symm bit]) (h.tm.windowRadius p (encIn a).length)

private theorem trInit_tail_length {K : Type} [DecidableEq K] {Γ : K → Type} (k : K)
    (input : List (Γ k)) : (TM2to1.trInit k input).tail.length ≤ input.length := by
  let mkCell : Γ k → TM2to1.Γ' K Γ :=
    fun a => (false, Function.update (fun _ => none) k (some a))
  change (input.reverse.map mkCell).tail.length ≤ input.length
  simp only [List.length_tail, List.length_map, List.length_reverse]
  omega

/-- The finite input window represents the original compiled initial configuration. -/
theorem inputWindow_toNative (h : TM2Computable encIn encBool f) (p : Polynomial ℕ) (a : α) :
    (h.inputWindow p a).toNative =
      TM0.init (TM2to1.trInit h.tm.k₀ (List.map h.inputAlphabet.symm (encIn a))) :=
  (ofList_toNative _ _ _).trans (TM0.init_eq _).symm

/-- The finite Boolean halt window represents the canonical native halt configuration. -/
theorem haltWindow_toNative (h : TM2Computable encIn encBool f) (p : Polynomial ℕ)
    (a : α) (bit : Bool) :
    (h.haltWindow p a bit).toNative = h.tm.toTM0Halt [h.outputAlphabet.symm bit] :=
  ofList_toNative _ _ _

private theorem inputWindow_fits (h : TM2Computable encIn encBool f)
    (p : Polynomial ℕ) (a : α) :
    (TM2to1.trInit h.tm.k₀ (List.map h.inputAlphabet.symm (encIn a))).tail.length ≤
      h.tm.windowRadius p (encIn a).length := by
  have ht := trInit_tail_length h.tm.k₀ (List.map h.inputAlphabet.symm (encIn a))
  simp only [List.length_map] at ht
  dsimp only [FinTM2.windowRadius]
  omega

private theorem haltWindow_fits (h : TM2Computable encIn encBool f)
    (p : Polynomial ℕ) (a : α) (bit : Bool) :
    (TM2to1.trInit h.tm.k₁ [h.outputAlphabet.symm bit]).tail.length ≤
      h.tm.windowRadius p (encIn a).length := by
  have ht := trInit_tail_length h.tm.k₁ [h.outputAlphabet.symm bit]
  simp only [List.length_cons, List.length_nil] at ht
  dsimp only [FinTM2.windowRadius]
  omega

private theorem inputWindow_right_length (h : TM2Computable encIn encBool f)
    (p : Polynomial ℕ) (a : α) :
    (h.inputWindow p a).right.length = h.tm.windowRadius p (encIn a).length :=
  ofList_right_length _ _ _ (inputWindow_fits h p a)

private theorem haltWindow_right_length (h : TM2Computable encIn encBool f)
    (p : Polynomial ℕ) (a : α) (bit : Bool) :
    (h.haltWindow p a bit).right.length = h.tm.windowRadius p (encIn a).length :=
  ofList_right_length _ _ _ (haltWindow_fits h p a bit)

/-- The complete initial window has polynomial size. -/
theorem inputWindow_size (h : TM2Computable encIn encBool f) (p : Polynomial ℕ) (a : α) :
    (h.inputWindow p a).size = h.tm.windowRadius p (encIn a).length + 2 :=
  ofList_size _ _ _ (inputWindow_fits h p a)

/-- The canonical Boolean target has exactly the same window size as the input. -/
theorem haltWindow_size (h : TM2Computable encIn encBool f) (p : Polynomial ℕ)
    (a : α) (bit : Bool) :
    (h.haltWindow p a bit).size = h.tm.windowRadius p (encIn a).length + 2 :=
  ofList_size _ _ _ (haltWindow_fits h p a bit)

/-- A canonical halt window is terminal for the actual finite-window transition function. -/
theorem haltWindow_terminal (h : TM2Computable encIn encBool f) (p : Polynomial ℕ)
    (a : α) (bit : Bool) :
    Turing.TM0Window.step h.tm.toTM0 (h.haltWindow p a bit) = none :=
  step_eq_none_of_native (by rw [haltWindow_toNative]; exact h.tm.toTM0Halt_terminal _)

/-- The initial finite window is computed in polynomial time from the original binary input. -/
theorem computableInPolyTime_inputWindow (h : TM2Computable encIn encBool f)
    [∀ k, Finite (h.tm.Γ k)] (p : Polynomial ℕ) :
    ComputableInPolyTime (h.inputWindow p) encIn
      (encCfg (Γ := TM2to1.Γ' h.tm.K h.tm.Γ) (Q := FinTM2.TM0Control h.tm)) := by
  exact computableInPolyTime_ofList (Γ := TM2to1.Γ' h.tm.K h.tm.Γ) (Q := FinTM2.TM0Control h.tm)
    (const default) h.computableInPolyTime_toTM0Input
    ((h.tm.computableInPolyTime_windowRadius p).comp (encoding_length encIn))

/-- The canonical Boolean target window is computed in polynomial time at the same width. -/
theorem computableInPolyTime_haltWindow (h : TM2Computable encIn encBool f)
    [∀ k, Finite (h.tm.Γ k)] (p : Polynomial ℕ) (bit : Bool) :
    ComputableInPolyTime (fun a => h.haltWindow p a bit) encIn
      (encCfg (Γ := TM2to1.Γ' h.tm.K h.tm.Γ) (Q := FinTM2.TM0Control h.tm)) := by
  exact computableInPolyTime_ofList (Γ := TM2to1.Γ' h.tm.K h.tm.Γ) (Q := FinTM2.TM0Control h.tm)
    (const _) (const _)
    ((h.tm.computableInPolyTime_windowRadius p).comp (encoding_length encIn))

private theorem headRange_toWindow (h : TM2Computable encIn encBool f) (p : Polynomial ℕ)
    (a : α) (bit : Bool)
    (hr : HeadPosition.ReachesWithin h.tm.toTM0 (-1)
      (p.eval (encIn a).length + TM2to1.headOverhead h.tm.m)
      ⟨TM0.init (TM2to1.trInit h.tm.k₀ (List.map h.inputAlphabet.symm (encIn a))), 0⟩
      ⟨h.tm.toTM0Halt [h.outputAlphabet.symm bit], 0⟩) :
    StateTransition.Reaches (Turing.TM0Window.step h.tm.toTM0)
      (h.inputWindow p a) (h.haltWindow p a bit) := by
  have hr' := hr.mono (show (-1 : ℤ) ≤ -1 from le_rfl)
    (show (p.eval (encIn a).length + TM2to1.headOverhead h.tm.m : ℤ) ≤
      (h.tm.windowRadius p (encIn a).length : ℤ) by
        dsimp only [FinTM2.windowRadius]
        omega)
  rw [← inputWindow_toNative h p a, ← haltWindow_toNative h p a bit] at hr'
  exact reaches_of_headRange hr' rfl (inputWindow_right_length h p a) rfl
    (haltWindow_right_length h p a bit)

end Turing.TM2Computable

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.TM0Window

/-- Standard PSPACE languages are exactly the accepting paths of the constructed fixed finite
single-tape machines inside their polynomially padded finite windows. -/
theorem mem_PSPACE_exists_windowTM0 {α : Type} {encIn : α ↪ List Bool} {A : Set α}
    (hA : A ∈ PSPACE encIn) :
    ∃ (f : α → Bool) (h : TM2Computable encIn encBool f), (∀ k, Finite (h.tm.Γ k)) ∧
      ∃ p : Polynomial ℕ, ∀ a, a ∈ A ↔
        StateTransition.Reaches (step h.tm.toTM0) (h.inputWindow p a) (h.haltWindow p a true) := by
  obtain ⟨f, h, hfinite, p, hp, hf, ht⟩ := mem_PSPACE_exists_boundedTM0 hA
  refine ⟨f, h, hfinite, p, fun a => ⟨fun ha => ?_, fun hr => ?_⟩⟩
  · exact h.headRange_toWindow p a true (by simpa only [(hf a).mp ha] using hp a)
  · apply (ht a).mpr
    simpa only [TM2Computable.inputWindow_toNative, TM2Computable.haltWindow_toNative] using
      reaches_native hr

end Cslib.Complexity
