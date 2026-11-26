/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Data.Finset.Lattice.Fold
public import CslibFrontier.Computability.Machines.Turing.SingleTape.TM0Restrict
import all CslibFrontier.Computability.Machines.Turing.SingleTape.TM0Restrict

/-!
# Head ranges for the Mathlib stack-machine compilation

Head coordinates record the visited cells of the standard `TM1to0` compilation. The coordinate
is auxiliary proof data; the machine and its tape are Mathlib's original objects.

## Main definitions

* `HeadPosition.Cfg`: a native single-tape configuration together with a head coordinate.
* `TM1.HeadRange`: bounds every elementary move within one structured statement.

## Main results

* `TM1to0.headRange_reaches`: the standard compiler executes a statement within its head range.
* `TM2to1.tr_reachesWithin_halt`: bounded stacks give a linear head range for the standard compiler.
-/

public section

namespace Turing

namespace HeadPosition

variable (Γ Q : Type*) [Inhabited Γ]

/-- A native configuration with its head coordinate relative to the initial head position. -/
structure Cfg where
  /-- The original configuration. -/
  native : TM0.Cfg Γ Q
  /-- The head coordinate. -/
  position : ℤ

variable {Γ Q}

section

variable [Inhabited Q]

/-- Execute the original instruction and update the auxiliary head coordinate. -/
@[expose] def step (M : TM0.Machine Γ Q) (c : Cfg Γ Q) : Option (Cfg Γ Q) :=
  (M c.native.q c.native.Tape.head).map fun (q, action) =>
    match action with
    | .write a => ⟨⟨q, c.native.Tape.write a⟩, c.position⟩
    | .move .left => ⟨⟨q, c.native.Tape.move .left⟩, c.position - 1⟩
    | .move .right => ⟨⟨q, c.native.Tape.move .right⟩, c.position + 1⟩

/-- A native step whose initial and final head coordinates lie in the supplied interval. -/
@[expose] def StepWithin (M : TM0.Machine Γ Q) (lo hi : ℤ) :
    Cfg Γ Q → Cfg Γ Q → Prop :=
  fun c d =>
    step M c = some d ∧ lo ≤ c.position ∧ c.position ≤ hi ∧
      lo ≤ d.position ∧ d.position ≤ hi

/-- The reflexive closure of native steps whose endpoints lie in the supplied interval. -/
@[expose] def ReachesWithin (M : TM0.Machine Γ Q) (lo hi : ℤ) :
    Cfg Γ Q → Cfg Γ Q → Prop :=
  Relation.ReflTransGen (StepWithin M lo hi)

/-- Forgetting coordinates recovers precisely the original machine step. -/
theorem step_native (M : TM0.Machine Γ Q) (c : Cfg Γ Q) :
    (step M c).map Cfg.native = TM0.step M c.native := by
  rcases c with ⟨⟨q, T⟩, p⟩
  rcases h : M q T.head with _ | ⟨q', ⟨_ | _⟩ | a⟩ <;>
    simp only [step, TM0.step, h, Option.map_none, Option.map_some]

/-- A bounded coordinate path is a path of the original single-tape machine. -/
theorem ReachesWithin.native {M : TM0.Machine Γ Q} {lo hi : ℤ} {c d : Cfg Γ Q}
    (h : ReachesWithin M lo hi c d) : TM0.Reaches M c.native d.native :=
  h.lift Cfg.native fun a _ hab => by simpa [hab.1] using (step_native M a).symm

/-- Enlarging the coordinate interval retains every bounded path. -/
theorem ReachesWithin.mono {M : TM0.Machine Γ Q} {lo hi lo' hi' : ℤ} {c d : Cfg Γ Q}
    (h : ReachesWithin M lo hi c d) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    ReachesWithin M lo' hi' c d :=
  Relation.ReflTransGen.mono (r := StepWithin M lo hi) (p := StepWithin M lo' hi') (fun _ _ hs =>
    ⟨hs.1, hlo.trans hs.2.1, hs.2.2.1.trans hhi,
      hlo.trans hs.2.2.2.1, hs.2.2.2.2.trans hhi⟩) c d h

private theorem transGen_of_step_eq {M : TM0.Machine Γ Q} {lo hi : ℤ}
    {a b c : Cfg Γ Q} (he : step M a = step M b) (hp : a.position = b.position)
    (h : Relation.TransGen (StepWithin M lo hi) b c) :
    Relation.TransGen (StepWithin M lo hi) a c := by
  obtain ⟨d, hd, hdc⟩ := Relation.TransGen.head'_iff.mp h
  exact Relation.TransGen.head'_iff.mpr ⟨d, ⟨he.trans hd.1, hp.symm ▸ hd.2⟩, hdc⟩

end

/-- Forget the finite-control restriction while retaining the head coordinate. -/
@[expose] def liftCfg {S : Set Q} (c : Cfg Γ S) : Cfg Γ Q :=
  ⟨TM0.liftCfg c.native, c.position⟩

@[simp]
theorem liftCfg_mk {S : Set Q} (q : S) (T : Tape Γ) (p : ℤ) :
    liftCfg (⟨⟨q, T⟩, p⟩ : Cfg Γ S) = (⟨⟨q.val, T⟩, p⟩ : Cfg Γ Q) := by
  rfl

theorem liftCfg_injective {S : Set Q} : Function.Injective (liftCfg (Γ := Γ) (S := S)) := by
  rintro ⟨⟨q, T⟩, p⟩ ⟨⟨q', T'⟩, p'⟩ h
  simpa only [liftCfg_mk, Cfg.mk.injEq, TM0.Cfg.mk.injEq, Subtype.val_inj] using h

section

variable [Inhabited Q]

/-- Restricting the finite control preserves the coordinate-instrumented step. -/
theorem step_liftCfg (M : TM0.Machine Γ Q) {S : Set Q} (hS : TM0.Supports M S)
    [Inhabited S] (c : Cfg Γ S) :
    (step (TM0.restrict M hS) c).map liftCfg = step M (liftCfg c) := by
  rcases c with ⟨⟨q, T⟩, p⟩
  rcases hM : M q.val T.head with _ | ⟨q', ⟨_ | _⟩ | a⟩ <;>
    simp only [step, TM0.restrict, liftCfg, TM0.liftCfg, hM, Option.pmap_none, Option.pmap_some,
      Option.map_none, Option.map_some]

/-- A bounded native path lifts to the machine restricted to any supporting finite control set. -/
theorem ReachesWithin.restrict {M : TM0.Machine Γ Q} {S : Set Q}
    (hS : TM0.Supports M S) [Inhabited S] {lo hi : ℤ} {c d : Cfg Γ Q}
    (h : ReachesWithin M lo hi c d) (c' : Cfg Γ S) (hc : liftCfg c' = c) :
    ∃ d' : Cfg Γ S, liftCfg d' = d ∧ ReachesWithin (TM0.restrict M hS) lo hi c' d' := by
  induction h with
  | refl => exact ⟨c', hc, .refl⟩
  | @tail b d _ hs ih =>
    obtain ⟨b', rfl, hr⟩ := ih
    have hm := step_liftCfg M hS b'
    rw [hs.1] at hm
    obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hm
    exact ⟨d', rfl, hr.tail ⟨hd', hs.2⟩⟩

end

end HeadPosition

namespace TM1

variable {Γ Λ σ : Type*} [Inhabited Γ]

/-- The final head coordinate after executing a structured statement. -/
@[expose] def headAfter : Stmt Γ Λ σ → σ → Tape Γ → ℤ → ℤ
  | .move .left q, v, T, p => headAfter q v (T.move .left) (p - 1)
  | .move .right q, v, T, p => headAfter q v (T.move .right) (p + 1)
  | .write f q, v, T, p => headAfter q v (T.write (f T.head v)) p
  | .load f q, v, T, p => headAfter q (f T.head v) T p
  | .branch f q r, v, T, p =>
      if f T.head v then headAfter q v T p else headAfter r v T p
  | .goto _, _, _, p => p
  | .halt, _, _, p => p

/-- Every tape head position visited while executing one structured statement is in `[lo, hi]`.
The endpoints include the initial and final positions. -/
@[expose] def HeadRange (lo hi : ℤ) : Stmt Γ Λ σ → σ → Tape Γ → ℤ → Prop
  | .move .left q, v, T, p =>
      lo ≤ p ∧ p ≤ hi ∧ HeadRange lo hi q v (T.move .left) (p - 1)
  | .move .right q, v, T, p =>
      lo ≤ p ∧ p ≤ hi ∧ HeadRange lo hi q v (T.move .right) (p + 1)
  | .write f q, v, T, p =>
      lo ≤ p ∧ p ≤ hi ∧ HeadRange lo hi q v (T.write (f T.head v)) p
  | .load f q, v, T, p => HeadRange lo hi q (f T.head v) T p
  | .branch f q r, v, T, p =>
      if f T.head v then HeadRange lo hi q v T p else HeadRange lo hi r v T p
  | .goto _, _, _, p => lo ≤ p ∧ p ≤ hi
  | .halt, _, _, p => lo ≤ p ∧ p ≤ hi

theorem HeadRange.endpoints {lo hi : ℤ} {q : Stmt Γ Λ σ} {v T p}
    (h : HeadRange lo hi q v T p) :
    (lo ≤ p ∧ p ≤ hi) ∧ (lo ≤ headAfter q v T p ∧ headAfter q v T p ≤ hi) := by
  induction q generalizing v T p with
  | move d q ih =>
    cases d <;> exact ⟨⟨h.1, h.2.1⟩, (ih h.2.2).2⟩
  | write f q ih => exact ⟨⟨h.1, h.2.1⟩, (ih h.2.2).2⟩
  | load f q ih => exact ih h
  | branch f q r ihq ihr =>
    cases hf : f T.head v <;> simp only [HeadRange, headAfter, hf, Bool.false_eq_true,
      ↓reduceIte] at h ⊢
    exacts [ihr h, ihq h]
  | goto _ | halt => exact ⟨h, h⟩

end TM1

namespace TM1to0

open HeadPosition

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ)

/-- Executing a structured statement through Mathlib's compiler respects every elementary head
range, including the intermediate configurations of the compiled single-tape machine. -/
theorem headRange_reaches {lo hi : ℤ} (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) (p : ℤ)
    (h : TM1.HeadRange lo hi q v T p) :
    Relation.TransGen (StepWithin (tr M) lo hi) ⟨⟨(some q, v), T⟩, p⟩
      ⟨trCfg M (TM1.stepAux q v T), TM1.headAfter q v T p⟩ := by
  induction q generalizing v T p with
  | move d q ih =>
    cases d <;>
      exact .head ⟨rfl, h.1, h.2.1, (TM1.HeadRange.endpoints h.2.2).1⟩ (ih _ _ _ h.2.2)
  | write f q ih => exact .head ⟨rfl, h.1, h.2.1, h.1, h.2.1⟩ (ih _ _ _ h.2.2)
  | load f q ih =>
    exact HeadPosition.transGen_of_step_eq
      (b := ⟨⟨(some q, f T.head v), T⟩, p⟩) rfl rfl (ih (f T.head v) T p h)
  | branch f q r ihq ihr =>
    cases hf : f T.head v <;>
      simp only [TM1.HeadRange, TM1.headAfter, TM1.stepAux, hf, Bool.false_eq_true,
        Bool.cond_false, Bool.cond_true, ↓reduceIte] at h ⊢
    · exact HeadPosition.transGen_of_step_eq (b := ⟨⟨(some r, v), T⟩, p⟩)
        (by simp only [HeadPosition.step, tr, trAux, hf, Bool.cond_false]) rfl (ihr v T p h)
    · exact HeadPosition.transGen_of_step_eq (b := ⟨⟨(some q, v), T⟩, p⟩)
        (by simp only [HeadPosition.step, tr, trAux, hf, Bool.cond_true]) rfl (ihq v T p h)
  | goto _ | halt =>
    exact .single ⟨by simp only [HeadPosition.step, tr, trAux, TM1.stepAux, trCfg,
      Option.map_none, Option.map_some, Tape.write_self]; rfl, h.1, h.2, h.1, h.2⟩

end TM1to0

namespace TM2to1

open HeadPosition

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

private def stackDepth : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q | .peek _ _ q | .pop _ _ q => stackDepth q + 1
  | .load _ q => stackDepth q
  | .branch _ q r => max (stackDepth q) (stackDepth r)
  | .goto _ | .halt => 0

private theorem stackDepth_run {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    stackDepth (stRun o q) = stackDepth q + 1 := by
  cases o <;> rfl

private theorem stWrite_length {k : K} (o : StAct K Γ σ k) (v : σ) (S : List (Γ k)) :
    (stWrite v S o).length ≤ S.length + 1 := by
  cases o <;> simp only [stWrite, List.length_cons, List.length_tail] <;> omega

private theorem TrCfg.right_unique {c : TM2.Cfg Γ Λ σ}
    {a b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ} (ha : TrCfg c a) (hb : TrCfg c b) : a = b := by
  rcases ha with @⟨q, v, S, L, hL⟩
  rcases hb with @⟨_, _, _, L', hL'⟩
  obtain rfl : L = L' := ListBlank.ext fun n => funext fun k => by
    simpa only [ListBlank.nth_map, proj, PointedMap.mk_val] using
      congrArg (fun T : ListBlank (Option (Γ k)) => T.nth n) ((hL k).trans (hL' k).symm)
  rfl

private theorem TrCfg.with_label {c : TM2.Cfg Γ Λ σ}
    {a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ} (h : TrCfg c a) (l : Option Λ) :
    TrCfg {c with l := l} {a with l := l.map Λ'.normal} := by
  cases h with
  | mk L hL => exact TrCfg.mk L hL

variable [DecidableEq K]

private theorem headRange_trStAct {R : ℤ} {k : K} (o : StAct K Γ σ k)
    (q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ) (v : σ) (T : Tape (Γ' K Γ)) (p : ℤ)
    (hp : 0 ≤ p) (hR : p + 1 ≤ R)
    (hq : ∀ v T p, -1 ≤ p → p ≤ R → TM1.HeadRange (-1) R q v T p) :
    TM1.HeadRange (-1) R (trStAct q o) v T p := by
  cases o with
  | push f | peek f =>
    exact ⟨by omega, by omega, by omega, by omega, hq _ _ _ (by omega) (by omega)⟩
  | pop f =>
    simp only [trStAct, TM1.HeadRange]
    cases T.head.1
    · exact ⟨by omega, by omega, by omega, by omega, hq _ _ _ (by omega) (by omega)⟩
    · exact hq _ _ _ (by omega) (by omega)

private theorem headAfter_trStAct {k : K} (o : StAct K Γ σ k)
    (q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (hq : ∀ v T p, TM1.headAfter q v T p = p) (v : σ) (S : ∀ k, List (Γ k))
    (L : ListBlank (∀ k, Option (Γ k))) :
    TM1.headAfter (trStAct q o) v
      ((Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))) (S k).length =
        (stWrite v (S k) o).length := by
  cases o with
  | push f => simp only [trStAct, TM1.headAfter, hq, stWrite, List.length_cons,
      Int.natCast_succ]
  | peek f => simp only [trStAct, TM1.headAfter, hq, stWrite]; omega
  | pop f =>
    simp only [trStAct, TM1.headAfter, stWrite]
    cases hs : S k with
    | nil =>
      simp only [List.length_nil, Function.iterate_zero, id_eq, Tape.mk'_head,
        addBottom_head_fst, ↓reduceIte, hq, List.tail_nil]
    | cons a s =>
      rw [List.length_cons, Tape.move_right_n_head, Tape.mk'_nth_nat,
        addBottom_nth_succ_fst]
      simp only [Bool.false_eq_true, ↓reduceIte, hq, List.tail_cons, Int.natCast_succ]; omega

variable [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM2.Stmt Γ Λ σ)

private abbrev compiler := TM1to0.tr (tr M)

private def atLabel (l : Λ' K Γ Λ σ) (v : σ) (T : Tape (Γ' K Γ)) (p : ℤ) :
    HeadPosition.Cfg (Γ' K Γ) (TM1to0.Λ' (tr M)) :=
  ⟨TM1to0.trCfg (tr M) ⟨some l, v, T⟩, p⟩

private theorem go_within {R : ℤ} {k : K} (o : StAct K Γ σ k)
    (q : TM2.Stmt Γ Λ σ) (v : σ) {S : List (Γ k)}
    {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n ≤ S.length) (hR : (S.length : ℤ) + 1 ≤ R) :
    ReachesWithin (compiler M) (-1) R
      (atLabel M (.go k o q) v (Tape.mk' ∅ (addBottom L)) 0)
      (atLabel M (.go k o q) v
        ((Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))) n) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    have hlt : n < S.length := by omega
    have hbit : (((Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))).head.2 k).isNone =
        false := by
      rw [Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd, stk_nth_val _ hL,
        List.getElem?_eq_getElem (by simpa only [List.length_reverse] using hlt)]
      rfl
    have hr := TM1to0.headRange_reaches (tr M) (tr M (.go k o q)) v
      ((Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))) n
      (lo := -1) (hi := R) (by
        simp only [tr, TM1.HeadRange, hbit, Bool.false_eq_true, ↓reduceIte]
        exact ⟨by omega, by omega, by omega, by omega⟩)
    have he : TM1.stepAux (tr M (.go k o q)) v
        ((Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))) =
        ⟨some (.go k o q), v,
          (Tape.move .right)^[n + 1] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [tr, TM1.stepAux, hbit, Bool.cond_false, Function.iterate_succ_apply']
    have hp : TM1.headAfter (tr M (.go k o q)) v
        ((Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))) n = (n + 1 : ℕ) := by
      simp only [tr, TM1.headAfter, hbit, Bool.false_eq_true, ↓reduceIte, Int.natCast_succ]
    rw [he, hp] at hr
    exact (ih (by omega)).trans hr.to_reflTransGen

private theorem ret_within {R : ℤ} (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) (hn : (n : ℤ) ≤ R) :
    ReachesWithin (compiler M) (-1) R
      (atLabel M (.ret q) v
        ((Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))) n)
      (atLabel M (.ret q) v (Tape.mk' ∅ (addBottom L)) 0) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    have hbit : ((Tape.move .right)^[n + 1] (Tape.mk' ∅ (addBottom L))).head.1 = false := by
      rw [Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_succ_fst]
    have hr := TM1to0.headRange_reaches (tr M) (tr M (.ret q)) v
      ((Tape.move .right)^[n + 1] (Tape.mk' ∅ (addBottom L))) (n + 1)
      (lo := -1) (hi := R) (by
        simp only [tr, TM1.HeadRange, hbit, Bool.false_eq_true, ↓reduceIte]
        exact ⟨by omega, by omega, by omega, by omega⟩)
    have he : TM1.stepAux (tr M (.ret q)) v
        ((Tape.move .right)^[n + 1] (Tape.mk' ∅ (addBottom L))) =
        ⟨some (.ret q), v, (Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      rw [tr, TM1.stepAux, hbit, Bool.cond_false]
      simp only [TM1.stepAux, Function.iterate_succ_apply', Tape.move_right_left]
    have hp : TM1.headAfter (tr M (.ret q)) v
        ((Tape.move .right)^[n + 1] (Tape.mk' ∅ (addBottom L))) (n + 1) = n := by
      simp only [tr, TM1.headAfter, hbit, Bool.false_eq_true, ↓reduceIte]; omega
    rw [he, hp] at hr
    exact hr.to_reflTransGen.trans (ih (by omega))

section

variable {R : ℤ} {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
  (S : ∀ k, List (Γ k)) (L : ListBlank (∀ k, Option (Γ k)))
  (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
  (hR : ((S k).length : ℤ) + 1 ≤ R)

include hL hR

private theorem action_within :
    ∃ L' : ListBlank (∀ k, Option (Γ k)),
      (∀ k', L'.map (proj k') = ListBlank.mk
        (((Function.update S k (stWrite v (S k) o)) k').map some).reverse) ∧
      ReachesWithin (compiler M) (-1) R
        (atLabel M (.go k o q) v
          ((Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))) (S k).length)
        (atLabel M (.ret q) (stVar v (S k) o)
          ((Tape.move .right)^[(stWrite v (S k) o).length]
            (Tape.mk' ∅ (addBottom L'))) (stWrite v (S k) o).length) := by
  obtain ⟨L', hL', he⟩ := tr_respects_aux₂ (q := TM1.Stmt.goto fun _ _ => .ret q) hL o
  refine ⟨L', hL', ?_⟩
  have hbit : (((Tape.move .right)^[(S k).length]
      (Tape.mk' ∅ (addBottom L))).head.2 k).isNone = true := by
    rw [Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd, stk_nth_val _ (hL k),
      List.getElem?_eq_none (by rw [List.length_reverse])]
    rfl
  have hr := TM1to0.headRange_reaches (tr M) (tr M (.go k o q)) v
    ((Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))) (S k).length
    (lo := -1) (hi := R) (by
      simp only [tr, TM1.HeadRange, hbit, ↓reduceIte]
      exact headRange_trStAct o _ v _ _ (by omega) hR fun _ _ _ hp hR => ⟨hp, hR⟩)
  have hout : TM1.stepAux (tr M (.go k o q)) v
      ((Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))) =
      ⟨some (.ret q), stVar v (S k) o,
        (Tape.move .right)^[(stWrite v (S k) o).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
    rw [tr, TM1.stepAux, hbit, Bool.cond_true, he]
    simp only [Function.update_self, TM1.stepAux]
  have hp : TM1.headAfter (tr M (.go k o q)) v
      ((Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))) (S k).length =
        (stWrite v (S k) o).length := by
    rw [tr, TM1.headAfter, hbit]
    exact headAfter_trStAct o _ (fun _ _ _ => rfl) v S L
  rw [hout, hp] at hr
  exact hr.to_reflTransGen

private theorem stackAction_within :
    ∃ L' : ListBlank (∀ k, Option (Γ k)),
      (∀ k', L'.map (proj k') = ListBlank.mk
        (((Function.update S k (stWrite v (S k) o)) k').map some).reverse) ∧
      Relation.TransGen (StepWithin (compiler M) (-1) R)
        ⟨⟨(some (trNormal (stRun o q)), v), Tape.mk' ∅ (addBottom L)⟩, 0⟩
        (atLabel M (.ret q) (stVar v (S k) o) (Tape.mk' ∅ (addBottom L')) 0) := by
  obtain ⟨L', hL', ha⟩ := action_within M o q v S L hL hR
  have hg := go_within M o q v (hL k) (S k).length le_rfl hR
  have hr := ret_within M q (stVar v (S k) o) L' (stWrite v (S k) o).length (R := R)
    (by have := stWrite_length o v (S k); omega)
  have h0R : (-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ R := by omega
  have hg0 : StepWithin (compiler M) (-1) R
      ⟨⟨(some (trNormal (stRun o q)), v), Tape.mk' ∅ (addBottom L)⟩, 0⟩
      (atLabel M (.go k o q) v (Tape.mk' ∅ (addBottom L)) 0) :=
    ⟨by simp only [trNormal_run, HeadPosition.step, atLabel, TM1to0.trCfg, compiler, TM1to0.tr,
      TM1to0.trAux, Option.map_some, Tape.write_self], h0R.1, h0R.2, h0R.1, h0R.2⟩
  exact ⟨L', hL', (Relation.TransGen.single hg0).trans_left (hg.trans (ha.trans hr))⟩

end

private theorem stmt_within {R : ℤ} (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) (L : ListBlank (∀ k, Option (Γ k))) (B : ℕ)
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (hB : ∀ k, (S k).length ≤ B) (hR : (B : ℤ) + stackDepth q + 1 ≤ R) :
    ∃ L' : ListBlank (∀ k, Option (Γ k)),
      (∀ k, L'.map (proj k) =
        ListBlank.mk (((TM2.stepAux q v S).stk k).map some).reverse) ∧
      Relation.TransGen (StepWithin (compiler M) (-1) R)
        ⟨⟨(some (trNormal q), v), Tape.mk' ∅ (addBottom L)⟩, 0⟩
        ⟨TM1to0.trCfg (tr M)
          ⟨(TM2.stepAux q v S).l.map Λ'.normal, (TM2.stepAux q v S).var,
            Tape.mk' ∅ (addBottom L')⟩, 0⟩ := by
  induction q using stmtStRec generalizing v S L B with
  | run k o q ih =>
    let S' := Function.update S k (stWrite v (S k) o)
    have hB' : ∀ k', (S' k').length ≤ B + 1 := fun k' => by
      by_cases hk : k' = k
      · subst k'
        simpa only [S', Function.update_self] using
          (stWrite_length o v (S k)).trans (Nat.add_le_add_right (hB k) 1)
      · simpa only [S', Function.update_of_ne hk] using (hB k').trans (Nat.le_add_right B 1)
    rw [stackDepth_run] at hR
    obtain ⟨L', hL', ha⟩ := stackAction_within M o q v S L hL (R := R) (by have := hB k; omega)
    obtain ⟨L'', hL'', hc⟩ := ih (stVar v (S k) o) S' L' (B + 1) hL' hB' (by omega)
    refine ⟨L'', by simpa only [step_run] using hL'', ?_⟩
    rw [step_run]
    exact ha.trans (HeadPosition.transGen_of_step_eq
      (b := ⟨⟨(some (trNormal q), stVar v (S k) o), Tape.mk' ∅ (addBottom L')⟩, 0⟩)
      (by simp only [HeadPosition.step, atLabel, TM1to0.trCfg, Option.map_some, tr,
        TM1to0.tr, TM1to0.trAux, Tape.mk'_head, addBottom_head_fst, Bool.cond_true]) rfl hc)
  | load f q ih =>
    obtain ⟨L', hL', hr⟩ := ih (f v) S L B hL hB hR
    exact ⟨L', hL', HeadPosition.transGen_of_step_eq
      (b := ⟨⟨(some (trNormal q), f v), Tape.mk' ∅ (addBottom L)⟩, 0⟩) rfl rfl hr⟩
  | branch f q r ihq ihr =>
    simp only [stackDepth] at hR
    have := Nat.le_max_left (stackDepth q) (stackDepth r)
    have := Nat.le_max_right (stackDepth q) (stackDepth r)
    cases hf : f v <;> simp only [TM2.stepAux, hf, Bool.cond_false, Bool.cond_true]
    · obtain ⟨L', hL', hc⟩ := ihr v S L B hL hB (by omega)
      exact ⟨L', hL', HeadPosition.transGen_of_step_eq
        (b := ⟨⟨(some (trNormal r), v), Tape.mk' ∅ (addBottom L)⟩, 0⟩)
        (by simp only [HeadPosition.step, trNormal, TM1to0.tr, TM1to0.trAux, hf,
          Bool.cond_false]) rfl hc⟩
    · obtain ⟨L', hL', hc⟩ := ihq v S L B hL hB (by omega)
      exact ⟨L', hL', HeadPosition.transGen_of_step_eq
        (b := ⟨⟨(some (trNormal q), v), Tape.mk' ∅ (addBottom L)⟩, 0⟩)
        (by simp only [HeadPosition.step, trNormal, TM1to0.tr, TM1to0.trAux, hf,
          Bool.cond_true]) rfl hc⟩
  | goto _ | halt =>
    have h0R : (-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ R := by omega
    exact ⟨L, hL, .single ⟨by simp only [HeadPosition.step, TM2.stepAux, TM1to0.trCfg, compiler,
      trNormal, TM1to0.tr, TM1to0.trAux, Option.map_some, Option.map_none, Tape.write_self],
      h0R.1, h0R.2, h0R.1, h0R.2⟩⟩

/-- The constant head-range overhead of the standard stack-machine compilation. -/
def headOverhead [Fintype Λ] : ℕ :=
  (Finset.univ.sup fun l => stackDepth (M l)) + 1

/-- A source computation with stacks of length at most `B` compiles to a native single-tape path
whose elementary head positions lie in `[-1, B + headOverhead M]`. Both endpoints have head
coordinate zero and encode the corresponding source stacks. -/
theorem tr_reachesWithin [Fintype Λ] {c d : TM2.Cfg Γ Λ σ}
    {a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ} (hca : TrCfg c a)
    (hr : TM2.Reaches M c d) (B : ℕ)
    (hB : ∀ e, TM2.Reaches M c e → ∀ k, (e.stk k).length ≤ B) :
    ∃ b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ, TrCfg d b ∧
      ReachesWithin (TM1to0.tr (tr M)) (-1) (B + headOverhead M)
        ⟨TM1to0.trCfg (tr M) a, 0⟩ ⟨TM1to0.trCfg (tr M) b, 0⟩ := by
  induction hr with
  | refl => exact ⟨a, hca, .refl⟩
  | @tail e d hce hed ih =>
    obtain ⟨b, heb, hpath⟩ := ih
    rcases heb with @⟨l, v, S, L, hL⟩
    cases l with
    | none => cases hed
    | some l =>
      obtain rfl : d = TM2.stepAux (M l) v S := Option.some.inj hed.symm
      obtain ⟨L', hL', hp⟩ := stmt_within M (M l) v S L B hL (hB _ hce)
        (R := B + headOverhead M) (by
          have := Finset.le_sup (f := fun l => stackDepth (M l)) (Finset.mem_univ l)
          simp only [headOverhead]; omega)
      exact ⟨_, TrCfg.mk L' hL', hpath.trans hp.to_reflTransGen⟩

private theorem trCfg_halt (k : K) (L : List (Γ k)) :
    TrCfg (⟨none, default, Function.update (fun _ => []) k L⟩ : TM2.Cfg Γ Λ σ)
      (⟨none, default, Tape.mk₁ (trInit k L)⟩ : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) := by
  exact (trCfg_init (Λ := Λ) (σ := σ) k L).with_label none

/-- The standard compiler reaches a canonical halted tape within a linear stack-space window.
The output may occupy a different designated stack from the input. -/
theorem tr_reachesWithin_halt [Fintype Λ] (ki ko : K) (input : List (Γ ki))
    (output : List (Γ ko))
    (hr : TM2.Reaches M (TM2.init ki input)
      ⟨none, default, Function.update (fun _ => []) ko output⟩) (B : ℕ)
    (hB : ∀ e, TM2.Reaches M (TM2.init ki input) e → ∀ k, (e.stk k).length ≤ B) :
    ReachesWithin (TM1to0.tr (tr M)) (-1) (B + headOverhead M)
      ⟨TM0.init (trInit ki input), 0⟩
      ⟨⟨(none, default), Tape.mk₁ (trInit ko output)⟩, 0⟩ := by
  obtain ⟨b, hb, hp⟩ := tr_reachesWithin M (trCfg_init ki input) hr B hB
  rwa [hb.right_unique (trCfg_halt ko output)] at hp

end TM2to1

end Turing
