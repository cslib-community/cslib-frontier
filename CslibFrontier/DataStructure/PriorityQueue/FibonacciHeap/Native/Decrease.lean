/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Cascade
import CslibFrontier.Tactic.Realize

/-!
# Native decrease-key source assembly

The original parent comparison selects either the already-certified cut/cascade source or no
structural update, followed by the existing key/minimum block. Runtime parent subtraction is
charged. The original forest proof supplies every reached-state domain on the valid indexed-heap
input.

## Main definitions

* `decreaseValid`: the existing allocated heap and valid present-key decrease conditions.

## Main results

* `realizes_decreaseKey`: the original linked decrease-key source through the native rules.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

private def cutCascade (d : Fin 4 → ℕ) : Memory.Prog Unit := do
  DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0) (cut (d 2) (d 3))
  DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
    (cascade (d 0 + 1) (d 3))

private def cutCascadeSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  cutSafe w d s ∧ cascadeSafe w ![d 0, d 1, d 3]
    ((Memory.spec 0).clientState s (DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (cut (d 2) (d 3))))

private theorem realizes_cutCascade : Realizes .exact cutCascade (.refl _)
    (WordEncoding.encode (α := Unit)) cutCascadeSafe (fun _ _ => 0) := by
  unfold cutCascade
  realize [realizes_cut, realizes_cascade]
  · exact h.1
  · exact h.2

private def decreasePrefix (d : Fin 4 → ℕ) : Memory.Prog Unit := do
  let pv ← Memory.read (d 1 + d 0 + d 2)
  if pv = 0 then pure ()
  else
    let p ← pure (pv - 1)
    let kp ← Memory.read (d 1 + p)
    if IndexedMinPQ.RawPrioLT (d 2, d 3) (p, kp) then
      cutCascade ![d 0, d 1, d 2, p]
    else pure ()

private def decreasePrefixSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
    (s.mem (d 1 + d 0 + d 2) ≠ 0 → s.mem (d 1 + d 0 + d 2) - 1 < d 0) ∧
    (s.mem (d 1 + d 0 + d 2) ≠ 0 →
      IndexedMinPQ.RawPrioLT (d 2, d 3)
        (s.mem (d 1 + d 0 + d 2) - 1, s.mem (d 1 + (s.mem (d 1 + d 0 + d 2) - 1))) →
      cutCascadeSafe w ![d 0, d 1, d 2, s.mem (d 1 + d 0 + d 2) - 1] s)

private theorem realizes_decreasePrefix : Realizes .exact decreasePrefix (.refl _)
    (WordEncoding.encode (α := Unit)) decreasePrefixSafe (fun _ _ => 0) := by
  unfold decreasePrefix
  realize [realizes_cutCascade]
  all_goals first
    | exact h.1.of_le (by have := h.2.1; omega)
    | exact h.1.of_le (by have := h.2.2.1 (by assumption); omega)
    | exact h.2.2.2 (by assumption) (by unfold IndexedMinPQ.RawPrioLT; omega)
    | omega

/-- Native decrease-key's entry and actual post-prefix minimum-pointer conditions. These are
compilation domains, not a replacement for the existing indexed-queue validity predicate. -/
private def decreaseSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  decreasePrefixSafe w d s ∧
    1 ≤ ((Memory.spec 0).clientState s (decreasePrefix d)).mem (d 1 + 9 * d 0 + 1)

private theorem decrease_source (d : Fin 4 → ℕ) :
    (do decreasePrefix d
        DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
          (setKey (d 2) (d 3))) =
      DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
        (decreaseKey (d 0) (d 2) (d 3)) := by
  simp only [decreasePrefix, DataStructure.link, decreaseKey, PFunctor.FreeM.liftM_bind,
    bind_assoc]
  congr 1 with pv : 1
  by_cases hpv : pv = 0
  · simp only [hpv, ite_true, ne_eq, not_true_eq_false, ite_false, pure_bind]
  · simp only [hpv, ite_false, ne_eq, not_false_eq_true, ite_true, pure_bind,
      PFunctor.FreeM.liftM_bind, bind_assoc]
    congr 1 with kp : 1
    by_cases hlt : IndexedMinPQ.RawPrioLT (d 2, d 3) (pv - 1, kp) <;>
      simp only [hlt, ite_true, ite_false, cutCascade, DataStructure.link,
        PFunctor.FreeM.liftM_bind, bind_assoc, pure_bind]
    rfl

/-- One uniform native emitter for the original complete decrease-key memory source. The
source's conditional structural changes, full memory effect and intrinsic history are retained. -/
private theorem realizes_decreaseKey_domain : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (decreaseKey (d 0) (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit)) decreaseSafe (fun _ _ => 0) :=
  (realizes_decreasePrefix.bind₀ <| realizes_setKey.reindex
    (fun d : (Fin 4 → ℕ) × Unit => d.1)
    (appendWords (.refl _) (WordEncoding.encode (α := Unit))) ![0, 1, 2, 3]
    fun _ i => by fin_cases i <;> rfl).congr decrease_source |>.consequence
      (fun _ _ _ _ _ h => ⟨h.1, h.1.1, h.1.2.1, h.2⟩) fun _ _ => le_rfl

private theorem sim_unit_wp {n w base : ℕ} {mem : Memory.State} {p : Prog Unit}
    {Q : Unit → (Cell → ℕ) → ℕ → Prop} (halloc : (layout n base).Inv mem)
    (hwp : Record.wp (Cell.ok n) w p Q ((layout n base).abs mem)) :
    (layout n base).Inv ((Memory.spec 0).clientState mem
      (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) p)) ∧
    ∃ r c, Q r ((layout n base).abs ((Memory.spec 0).clientState mem
      (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) p))) c := by
  obtain ⟨hrec, hpost⟩ := (Record.wp_iff _ _ _).mp hwp
  obtain ⟨_, _, habs, hi'⟩ := (Record.refinement (layout n base) w).simulates_client p halloc hrec
  dsimp only [Record.refinement] at habs hi'
  rw [clientState_width w, link_width (w := w)] at habs hi'
  exact ⟨hi', _, _, habs ▸ hpost⟩

private theorem cutCascade_domains {n K w base : ℕ} {mem : Memory.State}
    {v p : Fin n} (hfit : Fits w (base + (9 * n + 5)))
    (halloc : (layout n base).Inv mem) (hI : Inv n K ((layout n base).abs mem))
    (hv : (abs n ((layout n base).abs mem) v).isSome)
    (hpar : (view n ((layout n base).abs mem)).par v = p.val + 1) :
    cutCascadeSafe w ![n, base, v.val, p.val] mem ∧
      1 ≤ ((Memory.spec 0).clientState mem (cutCascade ![n, base, v.val, p.val])).mem
        (base + 9 * n + 1) := by
  have hn : Fits w n := hfit.of_le (by omega)
  obtain ⟨m, ts, hc⟩ := cascading_of_fibRawInv hI hv
  have hv_fn : v ∈ forestNodes ts := (hc.dom v).mpr hv
  obtain ⟨rtail, hcirc, hperm⟩ := hc.roots
  obtain ⟨hdp, hdp2, hdp_le, hroots, hnr, hnm⟩ := hc.cut_pre hperm hv_fn hpar
  have hv_ne : ∀ T ∈ ts, v ∈ T.nodes → T.root ≠ v := by grind
  have hwp : Record.wp (Cell.ok n) w (cut v p) (fun _ g' _ =>
      ∃ ts', Cascading n K (abs n ((layout n base).abs mem)) (view n g') v m (some p) ts' ∧
        (∃ T ∈ ts', T.root = v) ∧ (∀ T ∈ ts', p ∈ T.nodes → T.root ≠ v) ∧
        p ∈ forestNodes ts') ((layout n base).abs mem) :=
    wp_cut hdp hdp2 hdp_le hc.minRoot hcirc hroots hpar hn hnr hnm fun _ _ _ hcut =>
      hcut.cascading hc hperm (Or.inl rfl) (Or.inl rfl) hv_ne hv_fn hpar
  obtain ⟨hi', _, _, ts', hc', hv', hpv', hp'⟩ := sim_unit_wp halloc hwp
  have hsafe := cutSafe_of_cascading hfit halloc hc hv_fn hpar
  have hcas := cascadeSafe_of_cascading hfit hi' hc' hv' hpv' hp'
  have hfuel : (view n ((layout n base).abs _)).numMarked < n + 1 :=
    hc'.numMarked ▸ Nat.lt_succ_of_le (markedCount_le_n _)
  obtain ⟨_, _, _, _, hc'', _, _⟩ := sim_unit_wp hi' (wp_cascade hn (n + 1) hc' hv' hpv' hp' hfuel)
  have hmpos : 1 ≤ ((Memory.spec 0).clientState
      ((Memory.spec 0).clientState mem
        (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (cut v p)))
      (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
        (cascade (n + 1) p))).mem (base + 9 * n + 1) := by
    have hmin := hc''.minRoot
    change _ = m.val + 1 at hmin
    have hmin' : ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState mem
          (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (cut v p)))
        (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
          (cascade (n + 1) p))).mem (base + 9 * n + 1) = m.val + 1 := by
      simpa only [view, Record.Layout.abs, Cell.ok, ite_true, layout] using hmin
    omega
  refine ⟨⟨hsafe, hcas⟩, ?_⟩
  simpa only [cutCascade, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, StateTransitionSpec.clientState,
    ← PFunctor.FreeM.bind_eq_bind, StateTransitionSpec.runClient_bind] using hmpos

/-- The conventional valid indexed decrease-key domain over the existing allocated record
heap. The key and layout are runtime data; the existing source validity keeps its old bounds. -/
@[expose] def decreaseValid (w : ℕ) (d : Fin 4 → ℕ) (mem : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ (layout (d 0) (d 1)).Inv mem ∧
    ∃ (v : Fin (d 0)) (K k₀ : ℕ), v.val = d 2 ∧ Fits w K ∧
      Inv (d 0) K ((layout (d 0) (d 1)).abs mem) ∧
      abs (d 0) ((layout (d 0) (d 1)).abs mem) v = some k₀ ∧ d 3 ≤ k₀ ∧ d 3 ≤ K

private theorem decreaseSafe_of_valid {w : ℕ} {d : Fin 4 → ℕ} {mem : Memory.State}
    (h : decreaseValid w d mem) : decreaseSafe w d mem := by
  obtain ⟨hfit, halloc, v, K, k₀, hv, _, hI, hsv, _, _⟩ := h
  have hpres : (abs (d 0) ((layout (d 0) (d 1)).abs mem) v).isSome := by simp [hsv]
  obtain ⟨m, ts, hc⟩ := cascading_of_fibRawInv hI hpres
  have hcur : v ∈ forestNodes ts := (hc.dom v).mpr hpres
  have hvn : d 2 < d 0 := hv ▸ v.isLt
  have hpar_mem : (view (d 0) ((layout (d 0) (d 1)).abs mem)).par v =
      mem.mem (d 1 + d 0 + d 2) := by
    simp only [view, Record.Layout.abs, Cell.ok, layout, hv, hvn, ite_true]
  have hmin : 1 ≤ mem.mem (d 1 + 9 * d 0 + 1) := by
    have hm : mem.mem (d 1 + 9 * d 0 + 1) = m.val + 1 := by
      simpa only [view, Record.Layout.abs, Cell.ok, ite_true, layout] using hc.minRoot
    omega
  have parent (hp : mem.mem (d 1 + d 0 + d 2) ≠ 0) :
      ∃ p : Fin (d 0), mem.mem (d 1 + d 0 + d 2) = p.val + 1 := by
    obtain ⟨T, hT, hdesc⟩ := hc.desc_of_par hcur (hpar_mem ▸ hp)
    obtain ⟨p, _, hpar⟩ := (hc.valid T hT).1.par_of_mem_children v hdesc
    exact ⟨p, hpar_mem ▸ hpar⟩
  have hCC (p : Fin (d 0)) (hp : mem.mem (d 1 + d 0 + d 2) = p.val + 1) :
      cutCascadeSafe w ![d 0, d 1, d 2, p.val] mem ∧
      1 ≤ ((Memory.spec 0).clientState mem (cutCascade ![d 0, d 1, d 2, p.val])).mem
        (d 1 + 9 * d 0 + 1) := by
    simpa only [hv] using cutCascade_domains hfit halloc hI hpres (hpar_mem.trans hp)
  refine ⟨⟨hfit, hvn, ?_, ?_⟩, ?_⟩
  · intro hp; obtain ⟨p, hp⟩ := parent hp; rw [hp, Nat.add_sub_cancel]; exact p.isLt
  · intro hp _; obtain ⟨p, hp⟩ := parent hp; rw [hp, Nat.add_sub_cancel]; exact (hCC p hp).1
  simp only [decreasePrefix, StateTransitionSpec.clientState,
    StateTransitionSpec.runClient_lift_bind', Memory.read, Memory.step_read,
    StateTransitionSpec.stepFn]
  by_cases hp : mem.mem (d 1 + d 0 + d 2) = 0
  · simpa only [hp, ite_true, StateTransitionSpec.runClient_pure'] using hmin
  · obtain ⟨p, hp'⟩ := parent hp
    simp only [hp', Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, pure_bind,
      StateTransitionSpec.runClient_lift_bind', Memory.step_read, StateTransitionSpec.stepFn]
    by_cases hlt : IndexedMinPQ.RawPrioLT (d 2, d 3) (p.val, mem.mem (d 1 + p.val))
    · simp only [hlt, ite_true]; exact (hCC p hp').2
    · simpa only [hlt, ite_false, StateTransitionSpec.runClient_pure'] using hmin

/-- A uniform native decrease-key emitter on the original valid indexed-heap domain. The
existing heap/present-key/key-bound assumptions supply all reached-state compiler domains. -/
theorem realizes_decreaseKey : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (decreaseKey (d 0) (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit)) decreaseValid (fun _ _ => 0) :=
  realizes_decreaseKey_domain.consequence (fun _ _ _ _ _ h => decreaseSafe_of_valid h)
    (fun _ _ => le_rfl)

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
