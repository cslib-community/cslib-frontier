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
  obtain ⟨rfl, h⟩ := List.range'_inj.mp heq
  exact ⟨h.resolve_left (by omega), rfl⟩

private theorem gateWord_range_split {N g : ℕ} (p : Program prefixSignature N g)
    (k : Fin g) (wires : Fin 2 → Wire N g) (hline : p.lines k = ⟨.mul, wires⟩) {a b : ℕ}
    (hw : programWord p (.gate k) = List.range' a (b - a)) :
    ∃ m, a < m ∧ m < b ∧ programWord p (wires 0) = List.range' a (m - a) ∧
      programWord p (wires 1) = List.range' m (b - m) := by
  rw [programWord_gate_mul p k wires hline] at hw
  obtain ⟨hleft, hright, hw0, hw1⟩ := range_split_of_append
    (programWord_ne_nil p (wires 0)) (programWord_ne_nil p (wires 1)) hw
  refine ⟨a + (programWord p (wires 0)).length, by lia, by lia, ?_, ?_⟩
  · simpa only [Nat.add_sub_cancel_left] using hw0
  · simpa only [Nat.sub_add_eq] using hw1

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
  · have :=
      (List.range'_inj (s := i.val) (n := 1)).mp ((programWord_input p i).symm.trans hw)
    obtain rfl : b = a + 1 := by omega
    exact ⟨.leaf a, Nat.zero_le _, fun j hj => by
      simp only [ancMul_input, Finset.notMem_empty] at hj⟩
  · rw [programWord_gate_id p k wires hline] at hw
    obtain ⟨I, hd, hanc⟩ := ih0 a b hab hw
    rw [wireDepths_gate_id p k wires hline, ancMul_gate_id p k wires hline]
    exact ⟨I, by omega, hanc⟩
  · obtain ⟨m, ham, hmb, hw0, hw1⟩ := gateWord_range_split p k wires hline hw
    obtain ⟨IL, hdL, hancL⟩ := ih0 a m ham hw0
    obtain ⟨IR, hdR, hancR⟩ := ih1 m b hmb hw1
    refine ⟨.node IL IR, ?_, ?_⟩
    · rw [wireDepths_gate_mul p k wires hline]
      simp only [IntervalTree.depth]
      omega
    · intro j hj p₀ q₀ hpq hjw
      rw [ancMul_gate_mul p k wires hline, Finset.mem_insert, Finset.mem_union] at hj
      simp only [IntervalTree.intervals, Finset.mem_insert, Finset.mem_union]
      rcases hj with rfl | hj0 | hj1
      · obtain ⟨rfl, hlen⟩ := range'_eq_range'_iff (by omega) (hjw.symm.trans hw)
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
  · obtain ⟨rfl, h⟩ :=
      (List.range'_inj (s := i.val) (n := 1)).mp ((programWord_input p i).symm.trans hw)
    obtain rfl : i = ⟨0, hN⟩ := Fin.ext (h.resolve_left (by omega))
    refine ⟨fun _ => .input ⟨0, hN⟩, fun _ => .input ⟨0, hN⟩, fun _ => 1,
      rfl, rfl, rfl, rfl, fun d hd => ?_, fun j hj => ?_⟩
    · simp only [Program.wireDepths_input] at hd; omega
    · simp only [ancMul_input, Finset.notMem_empty] at hj
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
    obtain ⟨M₀, hM₀, hm, hw0, hw1⟩ := gateWord_range_split p k wires hline (a := 0) (b := M)
      (by simpa only [Nat.sub_zero] using hw)
    rw [Nat.sub_zero] at hw0
    set D₀ := p.wireDepths (wires 0)
    obtain ⟨v₀, u₀, T₀, hv0, hT0, hvD0, hTD0, hseg0, hanc0⟩ := ih0 M₀ hM₀ hw0 hlen0
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
      rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd_lt | rfl
      · obtain ⟨hTd_lt, ⟨sg₀, hsg₀, hvd_succ, hwires_d⟩, hrest⟩ := hseg0 d hd_lt
        simp only [v, u, T, show d ≠ D₀ + 1 by omega, show d + 1 ≠ D₀ + 1 by omega,
          show d ≠ D₀ by omega, ↓reduceIte]
        refine ⟨hTd_lt, ⟨sg₀, ?_, hvd_succ, hwires_d⟩, hrest⟩
        rwa [leftSpine_gate_mul p k wires hline, List.getElem?_append_left (by omega)]
      · simp only [v, u, T, show D₀ ≠ D₀ + 1 by omega, ↓reduceIte, hvD0, hTD0]
        refine ⟨hm, ⟨k, ?_, rfl, wires, hline, rfl, rfl⟩, rfl, hd1_le, hw0, hw1⟩
        simp only [leftSpine_gate_mul p k wires hline,
          List.getElem?_append_right (by rw [hlen0]), hlen0, Nat.sub_self,
          List.getElem?_cons_zero]
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
  | mk op wires => cases op <;> exact rank_lt_of_lines_eq p k h 0

/-- Every gate has depth strictly greater than its `firstInput` wire. -/
theorem wireDepths_firstInput_lt {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g) :
    p.wireDepths (firstInput (p.lines k)) + 1 ≤ p.wireDepths (.gate k) := by
  cases h : p.lines k with
  | mk op wires =>
    cases op
    · rw [wireDepths_gate_mul p k wires h, firstInput]; omega
    · rw [wireDepths_gate_id p k wires h, firstInput]

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

private theorem segChildren_nodup {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) : (segChildren c a b root w).Nodup :=
  (List.nodup_finRange c.size).filter _

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
  have hfi {p : Wire N c.size} {g : Fin c.size} (hg : g ∈ segChildren c a b root p) :
      firstInput (c.program.lines g) = p := ((mem_segChildren_iff c a b root p g).mp hg).2.1
  have hback {g : Fin c.size} (hg : g ∈ segChildren c a b root w)
      (hr : ReachesInSeg c a b root (.gate g) w) : False := by
    have hlt := rank_firstInput_lt c.program g
    rw [hfi hg] at hlt
    exact hlt.not_ge hr.rank_le
  induction h₁ with
  | refl =>
    cases h₂ with
    | refl => rfl
    | step hg' hsub => exact (hback hg₂ ((hfi hg').symm.trans (hfi hg₁) ▸ hsub)).elim
  | step hg' hsub₁ ih =>
    cases h₂ with
    | refl => exact (hback hg₁ ((hfi hg').symm.trans (hfi hg₂) ▸ hsub₁)).elim
    | step hg₂' hsub₂ => exact ih ((hfi hg₂').symm.trans (hfi hg') ▸ hsub₂)

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
  have ih (i : Fin (segChildren c a b root w).length) :=
    countWireInSeg_iff c a b root target (.gate (segChildren c a b root w)[i])
  have hmem (i : Fin (segChildren c a b root w).length) :
      (segChildren c a b root w)[i] ∈ segChildren c a b root w := List.getElem_mem _
  rw [countWireInSeg_def]
  refine ⟨fun hreach => ?_, fun hnreach => ?_⟩
  · by_cases hwt : w = target
    · rw [Finset.sum_eq_zero fun i _ => (ih i).2 fun hr =>
        (segChildren_rank_lt c a b root w i).not_ge (hwt ▸ hr.rank_le)]
      simp only [hwt, ↓reduceIte, Nat.add_zero]
    · obtain ⟨g, hg_mem, hg_sub⟩ := hreach.top_inversion.resolve_left (Ne.symm hwt)
      obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hg_mem
      rw [Fintype.sum_eq_single ⟨idx, hidx_lt⟩ fun i hne => (ih i).2 fun hi => hne <| Fin.ext <|
        (segChildren_nodup c a b root w).getElem_inj_iff.mp
          (ReachesInSeg.child_unique (hmem i) hg_mem hi hg_sub), (ih ⟨idx, hidx_lt⟩).1 hg_sub]
      simp only [hwt, ↓reduceIte, Nat.zero_add]
  · rw [Finset.sum_eq_zero fun i _ => (ih i).2 fun hi =>
      hnreach (ReachesInSeg.trans_step_top (hmem i) hi)]
    simp only [show w ≠ target from fun h => hnreach (h ▸ .refl w), ↓reduceIte, Nat.add_zero]
termination_by w => c.size - w.rank
decreasing_by
  have hlt := segChildren_rank_lt c a b root w i
  have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
  omega

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

/-- One unfolding of `countWireInSeg` inside a weighted sum of target multiplicities. -/
private theorem sum_countWireInSeg {N : ℕ} {ι : Type*} [Fintype ι] (c : PrefixCircuit N)
    (a b : ℕ) (root w : Wire N c.size) (P : ι → Prop) [DecidablePred P]
    (e : ι → Wire N c.size) :
    (∑ x, if P x then countWireInSeg c a b root (e x) w else 0) =
      (∑ x, if w = e x ∧ P x then 1 else 0) +
        ∑ i : Fin (segChildren c a b root w).length, ∑ x,
          if P x then countWireInSeg c a b root (e x) (.gate (segChildren c a b root w)[i])
          else 0 := by
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [countWireInSeg_def c a b root (e x) w]
  by_cases hP : P x <;> simp [hP]

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
  have ih (i : Fin (segChildren c a b root w).length) :=
    buildSegTree_counts c a b root (.gate (segChildren c a b root w)[i])
  have hst (v : Wire N c.size) : (buildSegTree c a b root v).state = wireState c.program v := by
    rw [buildSegTree_eq]; rfl
  rw [buildSegTree_eq]
  refine ⟨?_, fun s => ?_, fun m => ?_⟩
  · rw [GenPrefixTree.outCount, sum_countWireInSeg]
    simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, fun i => (ih i).1]
  · rw [GenPrefixTree.outAt, sum_countWireInSeg]
    simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, fun i => (ih i).2.1 s]
  -- Splitting off the visit of `v` itself relates the `mul`-gate sum to the one excluding `v`.
  have hsplit (v : Wire N c.size) :
      (∑ g, if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m then
          countWireInSeg c a b root (.gate g) v else 0) =
        (∑ g, if v = .gate g ∧ ((c.program.lines g).op = .mul ∧
          wireState c.program (.gate g) = m) then 1 else 0) +
        ∑ g, if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
          v ≠ .gate g then countWireInSeg c a b root (.gate g) v else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases h : v = .gate g
    · subst h; simp [countWireInSeg_eq_one_of_reaches (.refl _)]
    · simp [h]
  rw [GenPrefixTree.mulCount, (add_right_inj _).mp ((hsplit w).symm.trans
    (sum_countWireInSeg c a b root w _ Wire.gate))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(ih i).2.2 m, hsplit]
  simp only [hst, beq_iff_eq, Wire.gate.injEq, ite_and, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]
termination_by c.size - w.rank
decreasing_by
  have hlt := segChildren_rank_lt c a b root w i
  have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
  omega

private theorem segHasOut_le_card_outputs {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (w : Wire N c.size) :
    (if segHasOut c a b w then 1 else 0) ≤
      (Finset.univ.filter fun j : Fin N => c.outputs j = w).card := by
  by_cases h : segHasOut c a b w = true
  · obtain ⟨j, _, _, hjw⟩ := of_decide_eq_true h
    simp only [h, ↓reduceIte]
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjw⟩⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Nat.zero_le]

/-- Gates reading `w` as their `firstInput` occupy distinct input slots of `w`. -/
private theorem card_le_outDeg_of_firstInput {N : ℕ} (c : PrefixCircuit N) (w : Wire N c.size)
    (S : Finset (Fin c.size)) (hS : ∀ g ∈ S, firstInput (c.program.lines g) = w) :
    S.card ≤ c.outDeg w := by
  rw [c.outDeg_eq_card_filter]
  exact Finset.card_le_card_of_injOn (firstSlotOfGate c) (fun g hg => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (slotWire_firstSlotOfGate c g).trans (hS g hg)⟩)
    fun _ _ _ _ h => firstSlotOfGate_injective c h

/-- Active segment children plus segment output indicator at `w` do not exceed `wireFanout`. -/
theorem seg_fanout_bound {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) :
    (segChildren c a b root w).length + (if segHasOut c a b w then 1 else 0) ≤
      wireFanout c w := by
  have hdeg := card_le_outDeg_of_firstInput c w (segChildren c a b root w).toFinset fun g hg =>
    ((mem_segChildren_iff c a b root w g).mp (List.mem_toFinset.mp hg)).2.1
  rw [List.toFinset_card_of_nodup (segChildren_nodup c a b root _)] at hdeg
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
  have hdeg := card_le_outDeg_of_firstInput c root
    (insert sg (segChildren c a b root root).toFinset) fun g hg => by
      rcases Finset.mem_insert.mp hg with rfl | hg
      exacts [hsg_fi, ((mem_segChildren_iff c a b root root g).mp (List.mem_toFinset.mp hg)).2.1]
  rw [Finset.card_insert_of_notMem (mt List.mem_toFinset.mp hsg_not),
    List.toFinset_card_of_nodup (segChildren_nodup c a b root _)] at hdeg
  have hout := segHasOut_le_card_outputs c a b root
  rw [wireFanout]
  omega

end Cslib.Circuits.Prefix
