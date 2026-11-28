/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.PolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Compile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Polynomial-time compilation of arbitrary words

The encoded word pays for every new wire. A prefix invariant bounds the wire stack and edge
counter quadratically. The polynomial-time local vertex emitter supplies an output clock for
each layer; concatenating these outputs bounds the full compilation fold.

## Main results

* `Cslib.Complexity.NCL.Word.computableInPolyTime_run_empty`: polynomial-time word execution.
* `Cslib.Complexity.NCL.Word.computableInPolyTime_compile`: polynomial-time graph compilation.
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

private theorem Word.cost_prefix_le {w u : Word} (hu : u <+: w) : u.cost ≤ (encWord w).length := by
  obtain ⟨v, rfl⟩ := hu
  have h := Word.cost_le_length_encWord (u ++ v)
  simp only [Word.cost, List.map_append, List.sum_append] at h ⊢
  omega


end Cslib.Complexity.NCL

namespace Cslib.Complexity.NCL.Word

open _root_.Turing.MultiTapeTM

private abbrev encCore := encPair (encList encUnary) encUnary
private abbrev encVertices := encList (encVertex encNat)

private instance : ListEncoding encSlice encWord := by unfold encWord; infer_instance
private instance : SizedListEncoding encSlice encWord := by unfold encWord; infer_instance

private theorem computableInPolyTime_step :
    ComputableInPolyTime (fun p : Word.State × Slice => p.2.run p.1)
      (encPair Word.encState encSlice) Word.encState := by
  change ComputableInPolyTime
    ((fun p : Slice × Word.State => p.1.run p.2) ∘ (fun p : Word.State × Slice => (p.2, p.1)))
    (encPair Word.encState encSlice) Word.encState
  exact Slice.computableInPolyTime_run.comp
    ((ComputableInPolyTime.snd Word.encState encSlice).prod
      (ComputableInPolyTime.fst Word.encState encSlice))

private theorem computableInPolyTime_localVertices :
    ComputableInPolyTime (fun p : (List ℕ × ℕ) × Slice =>
      (p.2.run ⟨p.1.1, p.1.2, []⟩).verts)
      (encPair encCore encSlice) encVertices := by
  refine (Word.State.computableInPolyTime_verts.comp computableInPolyTime_step).comp
    ((Word.State.computableInPolyTime_mk ?_ ?_ (by fun_prop)).prod (ComputableInPolyTime.snd _ _))
  all_goals
    unfold encCore
    fun_prop

private theorem core_length_le (w : List ℕ) (n B : ℕ) (hn : n ≤ B) (hw : w.length ≤ B)
    (hb : ∀ e ∈ w, e ≤ n) : (encCore (w, n)).length ≤ 5 * (B + 1) ^ 2 := by
  have hl : (encList encUnary w).length ≤ w.length * (2 * B + 1) :=
    length_encList_le encUnary w (fun e he => by
      simpa only [encUnary_apply, List.length_replicate] using (hb e he).trans hn)
  have hm := Nat.mul_le_mul_right (2 * B + 1) hw
  simp only [encCore, length_encPair, encUnary_apply, List.length_replicate]
  nlinarith

private def coreBound (n : ℕ) : ℕ := 5 * (n + 1) ^ 2

private def vertexBound (c d n : ℕ) : ℕ := c * (2 * coreBound n + 1 + n + 1) ^ d

private def RunBound (c d : ℕ) (p consumed : Word) (st : Word.State) : Prop :=
  st.next ≤ consumed.cost ∧ st.wires.length ≤ consumed.cost ∧
    (∀ e ∈ st.wires, e ≤ st.next) ∧
    (encVertices st.verts).length ≤ consumed.length * vertexBound c d (encWord p).length

private theorem runBound_core {c d : ℕ} {p consumed : Word} {st : Word.State}
    (hp : consumed <+: p) (hs : RunBound c d p consumed st) :
    (encCore (st.wires, st.next)).length ≤ coreBound (encWord p).length := by
  have hn := Word.cost_prefix_le hp
  exact core_length_le _ _ _ (hs.1.trans hn) (hs.2.1.trans hn) hs.2.2.1



private theorem localVertices_le {c d : ℕ}
    (hcost : ∀ q : (List ℕ × ℕ) × Slice,
      (encVertices (q.2.run ⟨q.1.1, q.1.2, []⟩).verts).length ≤
        c * ((encPair encCore encSlice q).length + 1) ^ d)
    {p consumed : Word} {st : Word.State} {i : Slice}
    (hp : consumed <+: p) (hi : i ∈ p) (hs : RunBound c d p consumed st) :
    (encVertices (i.run ⟨st.wires, st.next, []⟩).verts).length ≤
      vertexBound c d (encWord p).length := by
  have hc := runBound_core hp hs
  have he := SizedListEncoding.length_elem_le (encA := encSlice) (encL := encWord) p i hi
  refine (hcost ((st.wires, st.next), i)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
  rw [length_encPair]
  dsimp only
  omega

private theorem runBound_step {c d : ℕ}
    (hcost : ∀ q : (List ℕ × ℕ) × Slice,
      (encVertices (q.2.run ⟨q.1.1, q.1.2, []⟩).verts).length ≤
        c * ((encPair encCore encSlice q).length + 1) ^ d)
    (p consumed : Word) (st : Word.State) (i : Slice)
    (hp : consumed ++ [i] <+: p) (hs : RunBound c d p consumed st) :
    RunBound c d p (consumed ++ [i]) (i.run st) := by
  obtain ⟨hn, hw, hb⟩ := Word.run_resources [i] st hs.2.2.1
  simp only [Word.run, List.foldl_cons, List.foldl_nil, Word.cost, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hn hw hb
  have hv := localVertices_le (i := i) hcost ((List.prefix_append consumed [i]).trans hp)
    (hp.subset (by simp)) hs
  have hn₀ := hs.1
  have hw₀ := hs.2.1
  refine ⟨?_, ?_, hb, ?_⟩
  · simp only [Word.cost, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton] at *
    omega
  · simp only [Word.cost, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton] at *
    omega
  · have hverts : (i.run st).verts = st.verts ++ (i.run ⟨st.wires, st.next, []⟩).verts := by
      simpa only [Word.run, List.foldl_cons, List.foldl_nil, List.append_nil] using
        congrArg Word.State.verts (Word.run_verts_append [i] ⟨st.wires, st.next, []⟩ st.verts)
    rw [hverts]
    simp only [encVertices, encList_append, List.length_append, List.length_singleton,
      Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add hs.2.2.2 hv

private theorem runBound_length {c d : ℕ} {p consumed : Word} {st : Word.State}
    (hp : consumed <+: p) (hs : RunBound c d p consumed st) :
    (Word.encState st).length ≤ 2 * coreBound (encWord p).length + 1 +
      (encWord p).length * vertexBound c d (encWord p).length := by
  have hc := runBound_core hp hs
  have hn : consumed.length ≤ (encWord p).length := hp.length_le.trans
    (SizedListEncoding.length_le (encA := encSlice) (encL := encWord) p)
  have hv := hs.2.2.2.trans (Nat.mul_le_mul_right _ hn)
  change (encPair encCore encVertices ((st.wires, st.next), st.verts)).length ≤ _
  rw [length_encPair]
  dsimp only
  omega


private def compileBound (c d n : ℕ) : ℕ :=
  2 * coreBound n + 1 + n * vertexBound c d n

private theorem compileBound_poly (c d : ℕ) : Cslib.PolynomiallyBounded (compileBound c d) := by
  unfold compileBound vertexBound coreBound
  fun_prop

private theorem runBound_nil (c d : ℕ) (p : Word) : RunBound c d p [] ⟨[], 0, []⟩ := by
  simp [RunBound, encVertices]

private theorem computableInPolyTime_run_of_bound (c d : ℕ)
    (hlocal : ∀ q : (List ℕ × ℕ) × Slice,
      (encVertices (q.2.run ⟨q.1.1, q.1.2, []⟩).verts).length ≤
        c * ((encPair encCore encSlice q).length + 1) ^ d) :
    ComputableInPolyTime (fun p : Word => run p ⟨[], 0, []⟩) encWord Word.encState := by
  unfold run
  exact (ComputableInPolyTime.foldl_spec (encA := encSlice) (encL := encWord)
    (encB := Word.encState) (list := id) (init := fun _ => Word.State.mk [] 0 [])
    (step := fun st i => i.run st)
    (size := fun p => compileBound c d (encWord p).length)
    ComputableInPolyTime.id' (ComputableInPolyTime.const _) computableInPolyTime_step
    (RunBound c d) (runBound_nil c d) (runBound_step hlocal)
    (PolyBounded.of_polynomiallyBounded (fun p => (encWord p).length)
      (compileBound_poly c d))
    (fun _ _ _ hp hs => runBound_length hp hs)).1


/-- Execute a complete structurally encoded word from the empty state in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_run_empty :
    ComputableInPolyTime (fun w : Word => w.run ⟨[], 0, []⟩) encWord Word.encState := by
  obtain ⟨c, d, hlocal⟩ := computableInPolyTime_localVertices.polyBounded_length.exists_le
  exact computableInPolyTime_run_of_bound c d hlocal

/-- Compile an arbitrary structurally encoded word in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_compile :
    ComputableInPolyTime Word.compile encWord encAndOrGraph := by
  have hv := Word.State.computableInPolyTime_verts.comp computableInPolyTime_run_empty
  have hn := Word.State.computableInPolyTime_next.comp computableInPolyTime_run_empty
  exact encAndOrGraph_mk_polyTime hv (ComputableInPolyTime.unary_to_binary.comp hn)

end Cslib.Complexity.NCL.Word
