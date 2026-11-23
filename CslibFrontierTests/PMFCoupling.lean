/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.Probability.PMF.Coupling

/-! # Module-boundary tests for `PMF.RepInv` and `PMF.HiddenCoupling` dot-combinators -/

set_option linter.privateModule false

namespace CslibFrontierTests.PMFCoupling

open Cslib.Probability.PMF

private noncomputable def loggedStep (step : PMF ℕ) (s : ℕ × List ℕ) : PMF (ℕ × List ℕ) :=
  step.map fun b => (s.1 + b, b :: s.2)

/-- `RepInv.pure`, `.of_eq`, `.bind`, `.map`, and `.iterate` infer intermediate distributions and
continuations across a module boundary while transporting `s.2.sum = s.1`. -/
private theorem repInv_loggedStep_iterate (step : PMF ℕ) (m : ℕ) :
    RepInv
      ((PMF.pure (0, [])).bind fun s₀ =>
        (Nat.iterate (fun d => d.bind (loggedStep step)) m (PMF.pure s₀)).bind (loggedStep step))
      ((PMF.pure 0).bind fun n₀ =>
        (Nat.iterate (fun d => d.bind fun n => step.map (n + ·)) m (PMF.pure n₀)).bind
          fun n => step.map (n + ·))
      Prod.fst (fun s => s.2.sum = s.1) := by
  have hstep : ∀ s : ℕ × List ℕ, s.2.sum = s.1 →
      RepInv (loggedStep step s) (step.map (s.1 + ·))
        Prod.fst (fun s' => s'.2.sum = s'.1) := fun s hs =>
    (RepInv.of_eq (PMF.map_id step)).map fun b _ _ => ⟨rfl, by simp [hs, Nat.add_comm]⟩
  exact (RepInv.pure (rep := Prod.fst) (inv := fun s : ℕ × List ℕ => s.2.sum = s.1) rfl rfl).bind
    fun s₀ _ hs₀ =>
      (RepInv.iterate (m := m) (init := s₀) (rep := Prod.fst)
        (fun _ s => s.2.sum = s.1) rfl hs₀ (fun _ _ s hs => hstep s hs)).bind
        fun s _ hs => hstep s hs

private noncomputable def explainBit (coin : PMF Bool) : Option Bool → PMF Bool
  | some b => PMF.pure b
  | none => coin

private noncomputable def lazyBitStep (coin : PMF Bool) (s : List Bool × Option Bool) :
    PMF (List Bool × Option Bool) :=
  match s.2 with
  | some b => PMF.pure (b :: s.1, some b)
  | none => coin.map fun b => (b :: s.1, some b)

/-- `HiddenCoupling.iterate`, `.pure`, `.bind`, `.bind_pure`, `.map`, and `.congr` couple `m + 1`
lazy bit reads followed by a fresh coin flip against eager sampling. -/
private theorem hiddenCoupling_lazyBit_pipeline (coin : PMF Bool) (m : ℕ) :
    HiddenCoupling
      ((Nat.iterate (fun d => d.bind (lazyBitStep coin)) m (PMF.pure ([], none))).bind fun s =>
        (lazyBitStep coin s).bind fun s' => coin.map fun extra => ((extra, s'.1), s'.2))
      coin (fun out => explainBit coin out.2) Prod.fst
      (fun k => (Nat.iterate (fun d => d.bind fun l => PMF.pure (k :: l)) m (PMF.pure [])).bind
        fun l => coin.map fun extra => (extra, k :: l))
      (fun out => ∀ b ∈ out.1.2, out.2 = some b) := by
  have hstep : ∀ s : List Bool × Option Bool, (∀ b ∈ s.1, s.2 = some b) →
      HiddenCoupling (lazyBitStep coin s) (explainBit coin s.2) (fun s' => explainBit coin s'.2)
        Prod.fst (fun k => PMF.pure (k :: s.1)) (fun s' => ∀ b ∈ s'.1, s'.2 = some b) := by
    rintro ⟨log, none | b⟩ hinv
    · exact ⟨by simp [lazyBitStep, explainBit, PMF.map], fun s' hs' b' hb' => by
        obtain ⟨b, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs'
        have hnil : log = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by cases hinv x hx
        subst hnil; simp [List.mem_singleton.mp hb']⟩
    · exact .pure rfl (fun _ hk => by rw [(PMF.mem_support_pure_iff b _).mp hk])
        fun b' hb' => (List.mem_cons.mp hb').elim (by rintro rfl; rfl) (hinv b')
  have hit : HiddenCoupling
      (Nat.iterate (fun d => d.bind (lazyBitStep coin)) m (PMF.pure ([], none)))
      coin (fun s => explainBit coin s.2) Prod.fst
      (fun k => Nat.iterate (fun d => d.bind fun l => PMF.pure (k :: l)) m (PMF.pure []))
      (fun s => ∀ b ∈ s.1, s.2 = some b) := by
    apply HiddenCoupling.iterate
      fun (_ : ℕ) (s : List Bool × Option Bool) => ∀ b ∈ s.1, s.2 = some b
    · rfl
    · exact fun _ _ => rfl
    · simp
    exact fun _ _ s hs => hstep s hs
  apply (hit.congr rfl (fun _ _ => rfl) fun _ _ h => h).bind
  intro s _ hs
  apply HiddenCoupling.bind_pure (f₂ := fun _ l' => coin.map fun extra => (extra, l')) (hstep s hs)
  intro s' _ hs'
  have hc : HiddenCoupling coin (explainBit coin s'.2) (fun _ => explainBit coin s'.2) id
      (fun _ => coin) (fun _ => True) :=
    ⟨by simp only [PMF.map, Function.comp_def]; exact PMF.bind_comm _ _ _, fun _ _ => trivial⟩
  apply hc.map; intro _ _ _
  exact ⟨rfl, fun _ _ => rfl, hs'⟩

end CslibFrontierTests.PMFCoupling
