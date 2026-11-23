/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.PMF.Coupling

/-! # Tests for `PMF.RepInv` and `PMF.HiddenCoupling` dot-combinators -/

namespace CslibFrontierTests.PMFCoupling

open Cslib.Probability.PMF

private noncomputable def loggedStep (step : PMF ℕ) (s : ℕ × List ℕ) : PMF (ℕ × List ℕ) :=
  step.map fun b => (s.1 + b, b :: s.2)

/-- `RepInv` `.of_eq`, `.bind`, `.map`, and `.iterate` infer intermediate distributions and
continuations while transporting `s.2.sum = s.1` across `m + 1` monadic steps. -/
theorem repInv_loggedStep_iterate (step : PMF ℕ) (m : ℕ) :
    RepInv
      ((Nat.iterate (fun d => d.bind (loggedStep step)) m (PMF.pure (0, []))).bind
        (loggedStep step))
      ((Nat.iterate (fun d => d.bind fun n => step.map (n + ·)) m
        (PMF.pure 0)).bind fun n => step.map (n + ·))
      Prod.fst (fun s => s.2.sum = s.1) := by
  have hstep : ∀ s : ℕ × List ℕ, s.2.sum = s.1 →
      RepInv (loggedStep step s) (step.map (s.1 + ·))
        Prod.fst (fun s' => s'.2.sum = s'.1) := fun s hs =>
    (RepInv.of_eq (PMF.map_id step)).map fun b _ _ => ⟨rfl, by simp [hs, Nat.add_comm]⟩
  exact (RepInv.iterate (m := m) (init := (0, [])) (rep := Prod.fst)
    (fun _ s => s.2.sum = s.1) rfl rfl (fun _ _ s hs => hstep s hs)).bind
    fun s _ hs => hstep s hs

private noncomputable def explainBit (coin : PMF Bool) : Option Bool → PMF Bool
  | some b => PMF.pure b
  | none => coin

private noncomputable def lazyBitStep (coin : PMF Bool) (s : List Bool × Option Bool) :
    PMF (List Bool × Option Bool) :=
  match s.2 with
  | some b => PMF.pure (b :: s.1, some b)
  | none => coin.map fun b => (b :: s.1, some b)

/-- `HiddenCoupling` `.pure`, `.congr`, `.map`, and `.iterate` couple `m` lazy reads of a cached
bit against a single eager draw from `coin`. -/
theorem hiddenCoupling_lazyBitStep_iterate (coin : PMF Bool) (m : ℕ) :
    HiddenCoupling
      (Nat.iterate (fun d => d.bind (lazyBitStep coin)) m (PMF.pure ([], none)))
      coin (fun s => explainBit coin s.2) Prod.fst
      (fun k => Nat.iterate (fun d => d.bind fun l => PMF.pure (k :: l)) m (PMF.pure []))
      (fun s => ∀ b ∈ s.1, s.2 = some b) := by
  apply HiddenCoupling.iterate fun (_ : ℕ) (s : List Bool × Option Bool) => ∀ b ∈ s.1, s.2 = some b
  · rfl
  · exact fun _ _ => rfl
  · simp
  rintro _ _ ⟨log, none | b⟩ hinv
  · exact ⟨by simp [lazyBitStep, explainBit, PMF.map], fun s' hs' b' hb' => by
      obtain ⟨b, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs'
      have hnil : log = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by cases hinv x hx
      subst hnil; simp [List.mem_singleton.mp hb']⟩
  · exact HiddenCoupling.pure rfl (fun _ hk => by rw [(PMF.mem_support_pure_iff b _).mp hk])
      fun b' hb' => (List.mem_cons.mp hb').elim (by rintro rfl; rfl) (hinv b')

end CslibFrontierTests.PMFCoupling
