/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Prefix.Basic
public import CslibFrontier.Computability.Circuit.Prefix.OptimalDepth.Trees
-- `import all`: reads private DAG decomposition helpers (`programWord`, `ancMul`, `leftSpine`)
-- from `Prefix.Basic`.
import all CslibFrontier.Computability.Circuit.Prefix.Basic
import CslibFrontier.Computability.Circuit.Basic
import CslibFrontier.Computability.Circuit.FanIn
import CslibFrontier.Computability.Circuit.Program

/-!
# Spine decomposition and segment tree construction on prefix DAGs

Left-spine decomposition (`spine_decomposition`), interval-tree extraction
(`exists_wireIntervalTree`), and unfolded segment distribution trees (`buildSegTree`) with
uniqueness of `firstInput` paths (`countWireInSeg_le_one`, `buildSegTree_counts`) and fanout budget
accounting (`seg_fanout_bound`, `seg_root_fanout_bound`) [Sergeev2025PrefixDepth].

## Main definitions

* `Cslib.Circuits.Prefix.segActive`, `Cslib.Circuits.Prefix.segChildren`: active wires and
  `firstInput` children for a principal-chain segment `[a, b)`.
* `Cslib.Circuits.Prefix.ReachesInSeg`, `Cslib.Circuits.Prefix.countWireInSeg`: segment path
  reachability and multiplicity counter.

## Main results

* `Cslib.Circuits.Prefix.ReachesInSeg.top_inversion`,
  `Cslib.Circuits.Prefix.countWireInSeg_le_one`: path unpacking and at-most-one multiplicity along
  active `firstInput` trees.
* `Cslib.Circuits.Prefix.seg_fanout_bound`,
  `Cslib.Circuits.Prefix.seg_root_fanout_bound`: wire-fanout bounds at interior segment wires and at
  the segment root.

## References

* [I. S. Sergeev, *A Note on the Depth of Optimal Fanout-Bounded Prefix
  Circuits*][Sergeev2025PrefixDepth]
-/

public section

namespace Cslib.Circuits.Prefix

/-- Nonempty contiguous integer ranges `List.range'` coincide iff their starts and lengths do. -/
theorem range'_eq_range'_iff {a₁ len₁ a₂ len₂ : ℕ} (h1 : 1 ≤ len₁)
    (heq : List.range' a₁ len₁ = List.range' a₂ len₂) : a₁ = a₂ ∧ len₁ = len₂ := by
  have hlen : len₁ = len₂ := by
    have := congrArg List.length heq
    simpa only [List.length_range'] using this
  subst hlen
  obtain ⟨m, rfl⟩ : ∃ m, len₁ = m + 1 := ⟨len₁ - 1, by omega⟩
  simp only [List.range'_succ, List.cons.injEq] at heq
  exact ⟨heq.1, rfl⟩


private theorem exists_wireIntervalTree {N g : ℕ} (p : Program prefixSignature N g)
    (w : Wire N g) :
    ∀ a b : ℕ, a < b → programWord p w = List.range' a (b - a) →
      ∃ I : IntervalTree a b,
        I.depth ≤ p.wireDepths w ∧
        ∀ j ∈ ancMul p w, ∀ p₀ q₀, p₀ < q₀ →
          programWord p (.gate j) = List.range' p₀ (q₀ - p₀) → (p₀, q₀) ∈ I.intervals := by
  refine prefix_wire_induction p
    (fun i a b hab hw => ?_)
    (fun k wires hline ih0 a b hab hw => ?_)
    (fun k wires hline ih0 ih1 a b hab hw => ?_) w
  · rw [programWord_input] at hw
    have hlen : b - a = 1 := by
      have := congrArg List.length hw
      simpa only [List.length_singleton, List.length_range'] using this.symm
    obtain rfl : b = a + 1 := by omega
    refine ⟨.leaf a, Nat.zero_le _, fun j hj => ?_⟩
    rw [ancMul_input] at hj
    exact absurd hj (Finset.notMem_empty j)
  · rw [programWord_gate_id p k wires hline] at hw
    obtain ⟨I, hd, hanc⟩ := ih0 a b hab hw
    refine ⟨I, ?_, ?_⟩
    · rw [wireDepths_gate_id p k wires hline]; omega
    · rw [ancMul_gate_id p k wires hline]; exact hanc
  · have hw_orig := hw
    rw [programWord_gate_mul p k wires hline] at hw
    obtain ⟨hm1, hm2, hw0, hw1⟩ := range_split_of_append
      (programWord_ne_nil p (wires 0)) (programWord_ne_nil p (wires 1)) hw
    set len0 := (programWord p (wires 0)).length
    set m := a + len0
    obtain ⟨IL, hdL, hancL⟩ :=
      ih0 a m (by omega) (by simpa only [m, Nat.add_sub_cancel_left] using hw0)
    obtain ⟨IR, hdR, hancR⟩ := ih1 m b (by omega) (by
      have hbm : b - m = b - a - len0 := by omega
      rw [hbm]
      exact hw1)
    refine ⟨.node IL IR, ?_, ?_⟩
    · rw [wireDepths_gate_mul p k wires hline]
      simp only [IntervalTree.depth]
      omega
    · intro j hj p₀ q₀ hpq hjw
      rw [ancMul_gate_mul p k wires hline, Finset.mem_insert, Finset.mem_union] at hj
      simp only [IntervalTree.intervals, Finset.mem_insert, Finset.mem_union]
      rcases hj with rfl | hj0 | hj1
      · obtain ⟨rfl, hlen⟩ := range'_eq_range'_iff (by omega) (hjw.symm.trans hw_orig)
        exact Or.inl (Prod.ext rfl (by omega))
      · exact Or.inr (Or.inl (hancL j hj0 p₀ q₀ hpq hjw))
      · exact Or.inr (Or.inr (hancR j hj1 p₀ q₀ hpq hjw))

private theorem spine_decomposition {N g : ℕ} (p : Program prefixSignature N g) (hN : 1 ≤ N) :
    ∀ (w : Wire N g) (M : ℕ), 1 ≤ M →
      programWord p w = List.range' 0 M →
      (leftSpine p w).length = p.wireDepths w →
      ∃ (v : ℕ → Wire N g) (u : ℕ → Wire N g) (T : ℕ → ℕ),
        v 0 = .input ⟨0, hN⟩ ∧
        T 0 = 1 ∧
        v (p.wireDepths w) = w ∧
        T (p.wireDepths w) = M ∧
        (∀ d < p.wireDepths w,
          T d < T (d + 1) ∧
          (∃ sg : Fin g,
            (leftSpine p w)[d]? = some sg ∧
            v (d + 1) = .gate sg ∧
            ∃ wires : Fin 2 → Wire N g,
              p.lines sg = ⟨.mul, wires⟩ ∧ wires 0 = v d ∧ wires 1 = u d) ∧
          p.wireDepths (v d) = d ∧
          p.wireDepths (u d) ≤ d ∧
          programWord p (v d) = List.range' 0 (T d) ∧
          programWord p (u d) = List.range' (T d) (T (d + 1) - T d)) ∧
        (∀ j ∈ ancMul p w,
          j ∈ leftSpine p w ∨ ∃ d < p.wireDepths w, j ∈ ancMul p (u d)) := by
  intro w
  refine prefix_wire_induction p
    (fun i M _ hw _ => ?_)
    (fun k wires hline _ M _ _ hlen => ?_)
    (fun k wires hline ih0 _ M _ hw hlen => ?_) w
  · rw [programWord_input] at hw
    have hM1 : M = 1 := by
      have := congrArg List.length hw
      simpa only [List.length_singleton, List.length_range'] using this.symm
    subst hM1
    simp only [List.range'_one, List.cons.injEq, and_true] at hw
    have hi0 : i = ⟨0, hN⟩ := Fin.ext hw
    subst hi0
    refine ⟨fun _ => .input ⟨0, hN⟩, fun _ => .input ⟨0, hN⟩, fun _ => 1,
      rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro d hd
      simp only [Program.wireDepths_input] at hd
      omega
    · intro j hj
      rw [ancMul_input] at hj
      exact absurd hj (Finset.notMem_empty j)
  · rw [leftSpine_gate_id p k wires hline, wireDepths_gate_id p k wires hline] at hlen
    have hle := leftSpine_length_le_wireDepths p (wires 0)
    omega
  · rw [leftSpine_gate_mul p k wires hline, List.length_append, List.length_singleton,
      wireDepths_gate_mul p k wires hline] at hlen
    have hle0 := leftSpine_length_le_wireDepths p (wires 0)
    have hlen0 : (leftSpine p (wires 0)).length = p.wireDepths (wires 0) := by omega
    have hd1_le : p.wireDepths (wires 1) ≤ p.wireDepths (wires 0) := by omega
    have hdepth_gate : p.wireDepths (.gate k) = p.wireDepths (wires 0) + 1 := by
      rw [wireDepths_gate_mul p k wires hline]; omega
    rw [programWord_gate_mul p k wires hline] at hw
    obtain ⟨hm1, hm2, hw0, hw1⟩ := range_split_of_append
      (programWord_ne_nil p (wires 0)) (programWord_ne_nil p (wires 1)) hw
    set M₀ := (programWord p (wires 0)).length
    set D₀ := p.wireDepths (wires 0)
    obtain ⟨v₀, u₀, T₀, hv0, hT0, hvD0, hTD0, hseg0, hanc0⟩ := ih0 M₀ (by omega) hw0 hlen0
    let v : ℕ → Wire N g := fun d => if d = D₀ + 1 then .gate k else v₀ d
    let u : ℕ → Wire N g := fun d => if d = D₀ then wires 1 else u₀ d
    let T : ℕ → ℕ := fun d => if d = D₀ + 1 then M else T₀ d
    refine ⟨v, u, T, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [v, Nat.zero_ne_add_one, ↓reduceIte, hv0]
    · simp only [T, Nat.zero_ne_add_one, ↓reduceIte, hT0]
    · simp only [v, hdepth_gate, ↓reduceIte]
    · simp only [T, hdepth_gate, ↓reduceIte]
    · intro d hd
      rw [hdepth_gate] at hd
      by_cases hd_eq : d = D₀
      · subst hd_eq
        have hsg : (leftSpine p (.gate k))[D₀]? = some k := by
          simp only [leftSpine_gate_mul p k wires hline,
            List.getElem?_append_right (by rw [hlen0]), hlen0, Nat.sub_self,
            List.getElem?_cons_zero]
        have hv_D0 : v D₀ = wires 0 := by
          simp only [v, show D₀ ≠ D₀ + 1 by omega, ↓reduceIte, hvD0]
        have hv_succ : v (D₀ + 1) = .gate k := by simp only [v, ↓reduceIte]
        have hu_D0 : u D₀ = wires 1 := by simp only [u, ↓reduceIte]
        have hT_D0 : T D₀ = M₀ := by
          simp only [T, show D₀ ≠ D₀ + 1 by omega, ↓reduceIte, hTD0]
        have hT_succ : T (D₀ + 1) = M := by simp only [T, ↓reduceIte]
        refine ⟨by omega, ⟨k, hsg, hv_succ, wires, hline, hv_D0.symm, hu_D0.symm⟩, ?_, ?_, ?_, ?_⟩
        · rw [hv_D0]
        · rw [hu_D0]; exact hd1_le
        · rw [hv_D0, hT_D0]; exact hw0
        · rw [hu_D0, hT_D0, hT_succ]; simpa only [Nat.zero_add] using hw1
      · have hd_lt : d < D₀ := by omega
        obtain ⟨hTd_lt, ⟨sg₀, hsg₀, hvd_succ, hwires_d⟩, hvd_d, hud_d, hvd_w, hud_w⟩ :=
          hseg0 d hd_lt
        have hsg : (leftSpine p (.gate k))[d]? = some sg₀ := by
          rw [leftSpine_gate_mul p k wires hline,
            List.getElem?_append_left (by rw [hlen0]; exact hd_lt)]
          exact hsg₀
        have hv_d : v d = v₀ d := by simp only [v, show d ≠ D₀ + 1 by omega, ↓reduceIte]
        have hv_s : v (d + 1) = v₀ (d + 1) := by
          simp only [v, show d + 1 ≠ D₀ + 1 by omega, ↓reduceIte]
        have hu_d : u d = u₀ d := by simp only [u, hd_eq, ↓reduceIte]
        have hT_d : T d = T₀ d := by simp only [T, show d ≠ D₀ + 1 by omega, ↓reduceIte]
        have hT_s : T (d + 1) = T₀ (d + 1) := by
          simp only [T, show d + 1 ≠ D₀ + 1 by omega, ↓reduceIte]
        refine ⟨by omega, ⟨sg₀, hsg, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
        · rw [hv_s]; exact hvd_succ
        · rw [hv_d, hu_d]; exact hwires_d
        · rw [hv_d]; exact hvd_d
        · rw [hu_d]; exact hud_d
        · rw [hv_d, hT_d]; exact hvd_w
        · rw [hu_d, hT_d, hT_s]; exact hud_w
    · intro j hj
      rw [ancMul_gate_mul p k wires hline, Finset.mem_insert, Finset.mem_union] at hj
      rw [leftSpine_gate_mul p k wires hline, List.mem_append, List.mem_singleton, hdepth_gate]
      rcases hj with rfl | hj0 | hj1
      · exact Or.inl (Or.inr rfl)
      · rcases hanc0 j hj0 with hsp | ⟨d, hd, hju⟩
        · exact Or.inl (Or.inl hsp)
        · refine Or.inr ⟨d, by omega, ?_⟩
          simpa only [u, show d ≠ D₀ by omega, ↓reduceIte] using hju
      · refine Or.inr ⟨D₀, by omega, ?_⟩
        simpa only [u, ↓reduceIte] using hj1

/-- First input wire `wires 0` read by a `{mul, id}` gate line. -/
@[expose] def firstInput {N g : ℕ} (l : Line prefixSignature N g) : Wire N g :=
  match l with
  | ⟨.id, wires⟩ => wires 0
  | ⟨.mul, wires⟩ => wires 0

private theorem rank_firstInput_lt {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g) :
    (firstInput (p.lines k)).rank < (Wire.gate k : Wire N g).rank := by
  cases h : p.lines k with
  | mk op wires =>
    cases op
    · exact rank_lt_of_lines_eq p k h 0
    · exact rank_lt_of_lines_eq p k h 0

/-- Every gate has depth strictly greater than its `firstInput` wire. -/
theorem wireDepths_firstInput_lt {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g) :
    p.wireDepths (firstInput (p.lines k)) + 1 ≤ p.wireDepths (.gate k) := by
  cases h : p.lines k with
  | mk op wires =>
    cases op
    · rw [wireDepths_gate_mul p k wires h]
      simp only [firstInput]
      omega
    · rw [wireDepths_gate_id p k wires h]
      simp only [firstInput]
      omega

private def firstSlotOfGate {N m : ℕ} (c : Circuit prefixSignature N m) (k : Fin c.size) :
    c.Slot :=
  ⟨k, match _h : (c.program.lines k).op with
    | .mul => 0
    | .id => 0⟩

private theorem slotWire_firstSlotOfGate {N m : ℕ} (c : Circuit prefixSignature N m)
    (k : Fin c.size) : c.slotWire (firstSlotOfGate c k) = firstInput (c.program.lines k) := by
  unfold firstSlotOfGate Circuit.slotWire firstInput
  dsimp only
  cases h : c.program.lines k with
  | mk op wires =>
    cases op <;> rfl

private theorem firstSlotOfGate_injective {N m : ℕ} (c : Circuit prefixSignature N m) :
    Function.Injective (firstSlotOfGate c) := by
  intro k₁ k₂ h
  exact congrArg Sigma.fst h


/-- Whether wire `w` is designated as an external output for some index in `[a, b)`. -/
@[expose] def segHasOut {N : ℕ} (c : PrefixCircuit N) (a b : ℕ) (w : Wire N c.size) : Bool :=
  decide (∃ j : Fin N, a ≤ j.val + 1 ∧ j.val + 1 < b ∧ c.outputs j = w)

/-- Whether wire `w` reaches an external output in `[a, b)` along non-root `firstInput` edges. -/
def segActive {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) : Bool :=
  segHasOut c a b w ||
    (List.finRange c.size).any fun g =>
      if _h : (Wire.gate g : Wire N c.size) ≠ root ∧
          firstInput (c.program.lines g) = w then
        segActive c a b root (.gate g)
      else
        false
termination_by c.size - w.rank
decreasing_by
  have hlt : w.rank < (Wire.gate g : Wire N c.size).rank := by
    rw [← _h.2]
    exact rank_firstInput_lt c.program g
  have hle := Wire.rank_le (Wire.gate g : Wire N c.size)
  omega

/-- Active non-root gates whose `firstInput` is `w`. -/
def segChildren {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) : List (Fin c.size) :=
  (List.finRange c.size).filter fun g =>
    decide ((Wire.gate g : Wire N c.size) ≠ root ∧ firstInput (c.program.lines g) = w) &&
      segActive c a b root (.gate g)

/-- Membership characterization of `segChildren c a b root w`. -/
theorem mem_segChildren_iff {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) (g : Fin c.size) :
    g ∈ segChildren c a b root w ↔
      (Wire.gate g : Wire N c.size) ≠ root ∧
        firstInput (c.program.lines g) = w ∧
        segActive c a b root (.gate g) = true := by
  simp only [segChildren, List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc]

/-- A wire is `segActive` iff it carries a segment output or has an active segment child. -/
theorem segActive_iff {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) :
    segActive c a b root w = true ↔
      segHasOut c a b w = true ∨ ∃ g, g ∈ segChildren c a b root w := by
  conv_lhs => unfold segActive
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and, mem_segChildren_iff]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    split_ifs at hg with h
    · exact ⟨g, h.1, h.2, hg⟩
  · rintro ⟨g, h1, h2, h3⟩
    refine ⟨g, ?_⟩
    split_ifs with h
    · exact h3
    · exact absurd ⟨h1, h2⟩ h

/-- Every gate in `segChildren c a b root w` has rank strictly greater than `w.rank`. -/
theorem segChildren_rank_lt {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) (i : Fin (segChildren c a b root w).length) :
    w.rank < (Wire.gate (segChildren c a b root w)[i] : Wire N c.size).rank := by
  have hmem : (segChildren c a b root w)[i] ∈ segChildren c a b root w := List.getElem_mem _
  obtain ⟨_, hfi, _⟩ := (mem_segChildren_iff c a b root w _).mp hmem
  have hlt := rank_firstInput_lt c.program (segChildren c a b root w)[i]
  rw [hfi] at hlt
  exact hlt

private def wireState {N g : ℕ} (p : Program prefixSignature N g) (w : Wire N g) : ℕ :=
  (programWord p w).length

private def buildSegTree {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) : GenPrefixTree :=
  GenPrefixTree.node
    (wireState c.program w)
    (segHasOut c a b w)
    (segChildren c a b root w).length
    (fun i => (c.program.lines (segChildren c a b root w)[i]).op == .mul)
    (fun i => buildSegTree c a b root (.gate (segChildren c a b root w)[i]))
termination_by c.size - w.rank
decreasing_by
  have hlt := segChildren_rank_lt c a b root w i
  have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
  omega

private theorem buildSegTree_eq {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) :
    buildSegTree c a b root w =
      GenPrefixTree.node
        (wireState c.program w)
        (segHasOut c a b w)
        (segChildren c a b root w).length
        (fun i => (c.program.lines (segChildren c a b root w)[i]).op == .mul)
        (fun i => buildSegTree c a b root (.gate (segChildren c a b root w)[i])) := by
  rw [buildSegTree]

/-- Reachability along `segChildren` edges inside a principal-chain segment. -/
inductive ReachesInSeg {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root : Wire N c.size) : Wire N c.size → Wire N c.size → Prop
  | refl (u : Wire N c.size) : ReachesInSeg c a b root u u
  | step {z p : Wire N c.size} {g : Fin c.size} :
      g ∈ segChildren c a b root p →
      ReachesInSeg c a b root z p →
      ReachesInSeg c a b root z (.gate g)

private theorem ReachesInSeg.rank_le {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root z u : Wire N c.size} (h : ReachesInSeg c a b root z u) : z.rank ≤ u.rank := by
  induction h with
  | refl => exact le_rfl
  | @step p g hg _ ih =>
    obtain ⟨_, hfi, _⟩ := (mem_segChildren_iff c a b root p g).mp hg
    have hlt : p.rank < (Wire.gate g : Wire N c.size).rank := by
      rw [← hfi]; exact rank_firstInput_lt c.program g
    omega

private theorem ReachesInSeg.trans_step_top {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root w : Wire N c.size} {g : Fin c.size} {u : Wire N c.size}
    (hg : g ∈ segChildren c a b root w)
    (hu : ReachesInSeg c a b root (.gate g) u) :
    ReachesInSeg c a b root w u := by
  induction hu with
  | refl => exact ReachesInSeg.step hg (ReachesInSeg.refl w)
  | step hg' _ ih => exact ReachesInSeg.step hg' ih

/-- Unpacks a `ReachesInSeg` path from `w` into `u = w` or a step through `segChildren`. -/
theorem ReachesInSeg.top_inversion {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root w u : Wire N c.size} (h : ReachesInSeg c a b root w u) :
    u = w ∨ ∃ g ∈ segChildren c a b root w, ReachesInSeg c a b root (.gate g) u := by
  induction h with
  | refl => exact Or.inl rfl
  | @step p g hg _ ih =>
    rcases ih with rfl | ⟨g₀, hg₀, hsub⟩
    · exact Or.inr ⟨g, hg, ReachesInSeg.refl (.gate g)⟩
    · exact Or.inr ⟨g₀, hg₀, ReachesInSeg.step hg hsub⟩

private theorem ReachesInSeg.child_unique {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root w u : Wire N c.size} {g₁ g₂ : Fin c.size}
    (hg₁ : g₁ ∈ segChildren c a b root w) (hg₂ : g₂ ∈ segChildren c a b root w)
    (h₁ : ReachesInSeg c a b root (.gate g₁) u) (h₂ : ReachesInSeg c a b root (.gate g₂) u) :
    g₁ = g₂ := by
  induction h₁ with
  | refl =>
    cases h₂ with
    | refl => rfl
    | step hg' hsub =>
      obtain ⟨_, hfi', _⟩ := (mem_segChildren_iff c a b root _ _).mp hg'
      obtain ⟨_, hfi₁, _⟩ := (mem_segChildren_iff c a b root w g₁).mp hg₁
      obtain ⟨_, hfi₂, _⟩ := (mem_segChildren_iff c a b root w g₂).mp hg₂
      have hp := hfi'.symm.trans hfi₁
      rw [hp] at hsub
      have hrk := hsub.rank_le
      have hlt : w.rank < (Wire.gate g₂ : Wire N c.size).rank :=
        hfi₂ ▸ rank_firstInput_lt c.program g₂
      omega
  | step hg' hsub₁ ih =>
    cases h₂ with
    | refl =>
      obtain ⟨_, hfi', _⟩ := (mem_segChildren_iff c a b root _ _).mp hg'
      obtain ⟨_, hfi₁, _⟩ := (mem_segChildren_iff c a b root w g₁).mp hg₁
      obtain ⟨_, hfi₂, _⟩ := (mem_segChildren_iff c a b root w g₂).mp hg₂
      have hp := hfi'.symm.trans hfi₂
      rw [hp] at hsub₁
      have hrk := hsub₁.rank_le
      have hlt : w.rank < (Wire.gate g₁ : Wire N c.size).rank :=
        hfi₁ ▸ rank_firstInput_lt c.program g₁
      omega
    | step hg₂' hsub₂ =>
      obtain ⟨_, hfi', _⟩ := (mem_segChildren_iff c a b root _ _).mp hg'
      obtain ⟨_, hfi₂', _⟩ := (mem_segChildren_iff c a b root _ _).mp hg₂'
      have hp := hfi₂'.symm.trans hfi'
      rw [hp] at hsub₂
      exact ih hsub₂

/-- `segActive` propagates forward along `ReachesInSeg`. -/
theorem ReachesInSeg.segActive_of {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root z u : Wire N c.size} (hz : segActive c a b root z = true)
    (h : ReachesInSeg c a b root z u) : segActive c a b root u = true := by
  induction h with
  | refl => exact hz
  | @step p g hg _ _ => exact ((mem_segChildren_iff c a b root p g).mp hg).2.2

/-- Multiplicity with which `target` is visited in the unfolded tree from `w`. -/
def countWireInSeg {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root target w : Wire N c.size) : ℕ :=
  (if w = target then 1 else 0) +
    ∑ i : Fin (segChildren c a b root w).length,
      countWireInSeg c a b root target (.gate (segChildren c a b root w)[i])
termination_by c.size - w.rank
decreasing_by
  have hlt := segChildren_rank_lt c a b root w i
  have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
  omega

private theorem countWireInSeg_def {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root target w : Wire N c.size) :
    countWireInSeg c a b root target w =
      (if w = target then 1 else 0) +
        ∑ i : Fin (segChildren c a b root w).length,
          countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) := by
  rw [countWireInSeg]

private theorem countWireInSeg_iff {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root target : Wire N c.size) :
    ∀ w : Wire N c.size,
      (ReachesInSeg c a b root w target → countWireInSeg c a b root target w = 1) ∧
      (¬ ReachesInSeg c a b root w target → countWireInSeg c a b root target w = 0) := by
  intro w
  have haux : ∀ rem, ∀ w : Wire N c.size, c.size - w.rank = rem →
      (ReachesInSeg c a b root w target → countWireInSeg c a b root target w = 1) ∧
      (¬ ReachesInSeg c a b root w target → countWireInSeg c a b root target w = 0) := by
    intro rem
    induction rem using Nat.strong_induction_on with
    | _ rem ih =>
      intro w hrem
      have hnodup : (segChildren c a b root w).Nodup := (List.nodup_finRange c.size).filter _
      have hch_ih : ∀ i : Fin (segChildren c a b root w).length,
          (ReachesInSeg c a b root (.gate (segChildren c a b root w)[i]) target →
            countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) = 1) ∧
          (¬ ReachesInSeg c a b root (.gate (segChildren c a b root w)[i]) target →
            countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) = 0) := by
        intro i
        have hlt := segChildren_rank_lt c a b root w i
        have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
        exact ih (c.size - (Wire.gate (segChildren c a b root w)[i] : Wire N c.size).rank)
          (by omega) (.gate (segChildren c a b root w)[i]) rfl
      refine ⟨fun hreach => ?_, fun hnreach => ?_⟩
      · rw [countWireInSeg_def]
        by_cases hwt : w = target
        · have hzero : ∀ i : Fin (segChildren c a b root w).length,
              countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) = 0 := by
            intro i
            refine (hch_ih i).2 fun hr => ?_
            have hrk := hr.rank_le
            have hlt := segChildren_rank_lt c a b root w i
            have hwt_rk : w.rank = target.rank := congrArg Wire.rank hwt
            omega
          rw [Finset.sum_eq_zero fun i _ => hzero i]
          simp only [hwt, ↓reduceIte, Nat.add_zero]
        · obtain ⟨g, hg_mem, hg_sub⟩ := (hreach.top_inversion).resolve_left (Ne.symm hwt)
          obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hg_mem
          let i₀ : Fin (segChildren c a b root w).length := ⟨idx, hidx_lt⟩
          have hi₀ : countWireInSeg c a b root target
              (.gate (segChildren c a b root w)[i₀]) = 1 := by
            refine (hch_ih i₀).1 ?_
            dsimp only [i₀]
            rw [Fin.getElem_fin, hidx_eq]
            exact hg_sub
          have hother : ∀ i : Fin (segChildren c a b root w).length, i ≠ i₀ →
              countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) = 0 := by
            intro i hne
            refine (hch_ih i).2 fun hi_sub => ?_
            have heq_g := ReachesInSeg.child_unique (List.getElem_mem _) hg_mem hi_sub hg_sub
            rw [← hidx_eq] at heq_g
            have heq_idx := (List.Nodup.getElem_inj_iff hnodup).mp heq_g
            exact hne (Fin.ext heq_idx)
          rw [Fintype.sum_eq_single i₀ hother, hi₀]
          simp only [hwt, ↓reduceIte, Nat.zero_add]
      · rw [countWireInSeg_def]
        have hwt : w ≠ target := fun heq => hnreach (heq ▸ ReachesInSeg.refl w)
        have hzero : ∀ i : Fin (segChildren c a b root w).length,
            countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) = 0 := by
          intro i
          exact (hch_ih i).2 fun hi_sub =>
            hnreach (ReachesInSeg.trans_step_top (List.getElem_mem _) hi_sub)
        rw [Finset.sum_eq_zero fun i _ => hzero i]
        simp only [hwt, ↓reduceIte, Nat.add_zero]
  exact haux (c.size - w.rank) w rfl

/-- Any wire reachable from `w` via `ReachesInSeg` has multiplicity `1` in `countWireInSeg`. -/
theorem countWireInSeg_eq_one_of_reaches {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root target w : Wire N c.size} (h : ReachesInSeg c a b root w target) :
    countWireInSeg c a b root target w = 1 :=
  (countWireInSeg_iff c a b root target w).1 h

private theorem countWireInSeg_eq_zero_of_not_reaches {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root target w : Wire N c.size} (h : ¬ ReachesInSeg c a b root w target) :
    countWireInSeg c a b root target w = 0 :=
  (countWireInSeg_iff c a b root target w).2 h

/-- Nonzero multiplicity in `countWireInSeg` implies `ReachesInSeg`. -/
theorem reaches_of_countWireInSeg_ne_zero {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root target w : Wire N c.size} (h : countWireInSeg c a b root target w ≠ 0) :
    ReachesInSeg c a b root w target := by
  by_contra hnr
  exact h (countWireInSeg_eq_zero_of_not_reaches hnr)

/-- Every wire has multiplicity at most `1` in `countWireInSeg`. -/
theorem countWireInSeg_le_one {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root target w : Wire N c.size) :
    countWireInSeg c a b root target w ≤ 1 := by
  by_cases h : ReachesInSeg c a b root w target
  · rw [countWireInSeg_eq_one_of_reaches h]
  · rw [countWireInSeg_eq_zero_of_not_reaches h]; omega

private theorem buildSegTree_counts {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) :
    (buildSegTree c a b root w).outCount =
      (∑ u : Wire N c.size, if segHasOut c a b u then countWireInSeg c a b root u w else 0) ∧
    (∀ s, (buildSegTree c a b root w).outAt s =
      ∑ u : Wire N c.size,
        if segHasOut c a b u ∧ wireState c.program u = s then
          countWireInSeg c a b root u w
        else 0) ∧
    (∀ m, (buildSegTree c a b root w).mulCount m =
      ∑ g : Fin c.size,
        if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧ w ≠ .gate g then
          countWireInSeg c a b root (.gate g) w
        else 0) := by
  have haux : ∀ rem, ∀ w : Wire N c.size, c.size - w.rank = rem →
      (buildSegTree c a b root w).outCount =
        (∑ u : Wire N c.size, if segHasOut c a b u then countWireInSeg c a b root u w else 0) ∧
      (∀ s, (buildSegTree c a b root w).outAt s =
        ∑ u : Wire N c.size,
          if segHasOut c a b u ∧ wireState c.program u = s then
            countWireInSeg c a b root u w
          else 0) ∧
      (∀ m, (buildSegTree c a b root w).mulCount m =
        ∑ g : Fin c.size,
          if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧ w ≠ .gate g then
            countWireInSeg c a b root (.gate g) w
          else 0) := by
    intro rem
    induction rem using Nat.strong_induction_on with
    | _ rem ih =>
      intro w hrem
      have hch_ih : ∀ i : Fin (segChildren c a b root w).length,
          (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).outCount =
            (∑ u : Wire N c.size,
              if segHasOut c a b u then
                countWireInSeg c a b root u (.gate (segChildren c a b root w)[i])
              else 0) ∧
          (∀ s, (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).outAt s =
            ∑ u : Wire N c.size,
              if segHasOut c a b u ∧ wireState c.program u = s then
                countWireInSeg c a b root u (.gate (segChildren c a b root w)[i])
              else 0) ∧
          (∀ m, (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).mulCount m =
            ∑ g : Fin c.size,
              if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
                  (Wire.gate (segChildren c a b root w)[i] : Wire N c.size) ≠ .gate g then
                countWireInSeg c a b root (.gate g) (.gate (segChildren c a b root w)[i])
              else 0) := by
        intro i
        have hlt := segChildren_rank_lt c a b root w i
        have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
        exact ih (c.size - (Wire.gate (segChildren c a b root w)[i] : Wire N c.size).rank)
          (by omega) (.gate (segChildren c a b root w)[i]) rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [buildSegTree_eq]
        simp only [GenPrefixTree.outCount]
        rw [Finset.sum_congr rfl fun i _ => (hch_ih i).1, Finset.sum_comm]
        have hw_split : (if segHasOut c a b w = true then 1 else 0) =
            ∑ u : Wire N c.size,
              if segHasOut c a b u = true then (if w = u then 1 else 0) else 0 := by
          rw [Fintype.sum_eq_single w]
          · simp only [↓reduceIte]
          · intro u hne; simp only [Ne.symm hne, ↓reduceIte, ite_self]
        rw [hw_split, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [countWireInSeg_def]
        by_cases hu : segHasOut c a b u = true
        · simp only [hu, ↓reduceIte]
        · simp only [hu, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero, Nat.add_zero]
      · intro s
        rw [buildSegTree_eq]
        simp only [GenPrefixTree.outAt]
        rw [Finset.sum_congr rfl fun i _ => (hch_ih i).2.1 s, Finset.sum_comm]
        have hw_split : (if segHasOut c a b w = true ∧ wireState c.program w = s then 1 else 0) =
            ∑ u : Wire N c.size,
              if segHasOut c a b u = true ∧ wireState c.program u = s then
                (if w = u then 1 else 0)
              else 0 := by
          rw [Fintype.sum_eq_single w]
          · simp only [↓reduceIte]
          · intro u hne; simp only [Ne.symm hne, ↓reduceIte, ite_self]
        rw [hw_split, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [countWireInSeg_def]
        by_cases hu : segHasOut c a b u = true ∧ wireState c.program u = s
        · simp only [hu, and_self, ↓reduceIte]
        · simp only [hu, ↓reduceIte, Finset.sum_const_zero, Nat.add_zero]
      · intro m
        rw [buildSegTree_eq]
        simp only [GenPrefixTree.mulCount, beq_iff_eq]
        have hstep : ∀ i : Fin (segChildren c a b root w).length,
            ((if (c.program.lines (segChildren c a b root w)[i]).op = .mul ∧
                (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).state = m then 1
              else 0) +
              (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).mulCount m) =
            ∑ g : Fin c.size,
              if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
                  w ≠ .gate g then
                countWireInSeg c a b root (.gate g) (.gate (segChildren c a b root w)[i])
              else 0 := by
          intro i
          let gi := (segChildren c a b root w)[i]
          have hmem : gi ∈ segChildren c a b root w := List.getElem_mem _
          obtain ⟨_, hfi, _⟩ := (mem_segChildren_iff c a b root w gi).mp hmem
          have hne_w : w ≠ .gate gi := by
            intro heq
            have hlt := rank_firstInput_lt c.program gi
            rw [hfi, heq] at hlt
            omega
          have hst_eq : (buildSegTree c a b root (.gate gi)).state =
              wireState c.program (.gate gi) := by
            rw [buildSegTree_eq]
            rfl
          change ((if (c.program.lines gi).op = .mul ∧
                (buildSegTree c a b root (.gate gi)).state = m then 1 else 0) +
              (buildSegTree c a b root (.gate gi)).mulCount m) =
            ∑ g : Fin c.size,
              if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
                  w ≠ .gate g then
                countWireInSeg c a b root (.gate g) (.gate gi)
              else 0
          rw [hst_eq, (hch_ih i).2.2 m]
          have hhead : (if (c.program.lines gi).op = .mul ∧
                wireState c.program (.gate gi) = m then 1 else 0) =
              ∑ g : Fin c.size,
                if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
                    g = gi then 1 else 0 := by
            rw [Fintype.sum_eq_single gi]
            · simp only [and_true]
            · intro g hne; simp only [hne, and_false, ↓reduceIte]
          rw [hhead, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun g _ => ?_
          change _ + (if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
              (Wire.gate gi : Wire N c.size) ≠ .gate g then
                countWireInSeg c a b root (.gate g) (.gate gi) else 0) = _
          by_cases hopm : (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m
          · rcases hopm with ⟨hop, hwm⟩
            by_cases hgi : g = gi
            · rw [hgi]
              have hself : countWireInSeg c a b root (.gate gi) (.gate gi) = 1 :=
                countWireInSeg_eq_one_of_reaches (ReachesInSeg.refl _)
              rw [hself]
              rw [hgi] at hop hwm
              simp only [hop, hwm, ne_eq, not_true_eq_false, and_false, and_true, ↓reduceIte,
                hne_w, not_false_eq_true, Nat.add_zero]
            · have hgate_ne : (Wire.gate gi : Wire N c.size) ≠ .gate g := fun h =>
                hgi (Wire.gate.inj h).symm
              by_cases hgw : w = .gate g
              · have hzero : countWireInSeg c a b root (.gate g) (.gate gi) = 0 := by
                  apply countWireInSeg_eq_zero_of_not_reaches
                  intro hr
                  have hrk := hr.rank_le
                  have hlt := rank_firstInput_lt c.program gi
                  rw [hfi, hgw] at hlt
                  omega
                rw [hzero]
                simp only [hgi, hgw, ne_eq, not_true_eq_false, and_false, ↓reduceIte, ite_self]
              · simp only [hop, hwm, hgi, and_false, hgate_ne, hgw, ne_eq, not_false_eq_true,
                  and_true, ↓reduceIte, Nat.zero_add]
          · have hf1 : ¬ ((c.program.lines g).op = .mul ∧
                wireState c.program (.gate g) = m ∧ g = gi) := fun h => hopm ⟨h.1, h.2.1⟩
            have hf2 : ¬ ((c.program.lines g).op = .mul ∧
                wireState c.program (.gate g) = m ∧
                  (Wire.gate gi : Wire N c.size) ≠ .gate g) := fun h => hopm ⟨h.1, h.2.1⟩
            have hf3 : ¬ ((c.program.lines g).op = .mul ∧
                wireState c.program (.gate g) = m ∧ w ≠ .gate g) := fun h => hopm ⟨h.1, h.2.1⟩
            simp only [hf1, hf2, hf3, ↓reduceIte]
        rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [countWireInSeg_def]
        by_cases hc : (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
            w ≠ .gate g
        · rcases hc with ⟨hc1, hc2, hc3⟩
          have hwg : ¬ (w = .gate g) := hc3
          simp only [hc1, hc2, hwg, ne_eq, not_false_eq_true, and_self, ↓reduceIte, Nat.zero_add]
        · simp only [hc, ↓reduceIte, Finset.sum_const_zero]
  exact haux (c.size - w.rank) w rfl

private theorem segHasOut_le_card_outputs {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (w : Wire N c.size) :
    (if segHasOut c a b w then 1 else 0) ≤
      (Finset.univ.filter fun j : Fin N => c.outputs j = w).card := by
  by_cases h : segHasOut c a b w = true
  · simp only [h, ↓reduceIte]
    simp only [segHasOut, decide_eq_true_eq] at h
    obtain ⟨j, _, _, hjw⟩ := h
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjw⟩⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Nat.zero_le]

/-- Active segment children plus segment output indicator at `w` do not exceed `wireFanout`. -/
theorem seg_fanout_bound {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) :
    (segChildren c a b root w).length + (if segHasOut c a b w then 1 else 0) ≤
      wireFanout c w := by
  set ch := segChildren c a b root w
  have hnodup : ch.Nodup := (List.nodup_finRange c.size).filter _
  have hdeg : ch.length ≤ c.outDeg w := by
    rw [c.outDeg_eq_card_filter, ← List.toFinset_card_of_nodup hnodup]
    refine Finset.card_le_card_of_injOn (firstSlotOfGate c) ?_ ?_
    · intro g hg
      rw [Finset.mem_coe, List.mem_toFinset, mem_segChildren_iff] at hg
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (slotWire_firstSlotOfGate c g).trans hg.2.1⟩
    · intro g₁ _ g₂ _ h
      exact firstSlotOfGate_injective c h
  have hout := segHasOut_le_card_outputs c a b w
  rw [wireFanout]
  omega

/-- At the segment root, reserving the next principal-chain gate `sg` leaves budget `≤ k - 1`. -/
theorem seg_root_fanout_bound {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root : Wire N c.size) (sg : Fin c.size)
    (hsg_fi : firstInput (c.program.lines sg) = root)
    (hsg_not : sg ∉ segChildren c a b root root) :
    (segChildren c a b root root).length + (if segHasOut c a b root then 1 else 0) + 1 ≤
      wireFanout c root := by
  set ch := segChildren c a b root root
  have hnodup : ch.Nodup := (List.nodup_finRange c.size).filter _
  have hsg_not_fin : sg ∉ ch.toFinset := by rw [List.mem_toFinset]; exact hsg_not
  have hdeg : ch.length + 1 ≤ c.outDeg root := by
    rw [c.outDeg_eq_card_filter, ← List.toFinset_card_of_nodup hnodup,
      ← Finset.card_insert_of_notMem hsg_not_fin]
    refine Finset.card_le_card_of_injOn (firstSlotOfGate c) ?_ ?_
    · intro g hg
      rw [Finset.mem_coe, Finset.mem_insert, List.mem_toFinset, mem_segChildren_iff] at hg
      rw [Finset.mem_coe, Finset.mem_filter]
      rcases hg with rfl | hg
      · exact ⟨Finset.mem_univ _, (slotWire_firstSlotOfGate c g).trans hsg_fi⟩
      · exact ⟨Finset.mem_univ _, (slotWire_firstSlotOfGate c g).trans hg.2.1⟩
    · intro g₁ _ g₂ _ h
      exact firstSlotOfGate_injective c h
  have hout := segHasOut_le_card_outputs c a b root
  rw [wireFanout]
  omega


end Cslib.Circuits.Prefix
