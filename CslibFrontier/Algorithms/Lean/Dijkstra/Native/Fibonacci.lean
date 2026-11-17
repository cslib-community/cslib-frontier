/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Fibonacci.Cost
public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Export
import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Backend
import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Initialize
import CslibFrontier.Algorithms.WordRAM.Dijkstra.ListEncode
import CslibFrontier.Tactic.Realize

/-!
# Native Fibonacci-heap Dijkstra from the existing framed memory client

The existing uniform method certificates realize the original linked source. Reached domains
come from the shared framed refinement and valid remaining Dijkstra histories. The original
amortized potential pays for memory operations; the native code separately charges arithmetic,
argument copies, loop control and initialization. Flat exports retain the original graph input
and word envelope, include their real prefix and halt, and preserve the full final memory.

## Main results

* `realizes_run`: one uniform emitter for the original allocated Fibonacci memory client.
* `exists_program_state`: its sharper halt-inclusive flat clock and exact whole-state export.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network
  optimization algorithms*][FredmanTarjan1987]
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.Dijkstra (ListInstance)
open Cslib.Algorithms.WordRAM.Dijkstra (encodeDist)

private def insertWord (e : ℕ × ℕ) (v k : ℕ) : Memory.Prog Unit :=
  link ((FibonacciHeap.layout e.1 e.2).methods 0) (FibonacciHeap.insert v k)

private def decreaseWord (e : ℕ × ℕ) (v k : ℕ) : Memory.Prog Unit :=
  link ((FibonacciHeap.layout e.1 e.2).methods 0) (FibonacciHeap.decreaseKey e.1 v k)

private theorem insert_realizes : Realizes .exact
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => insertWord d.1.1 d.1.2 d.2)
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
    (fun w d _ => Fits w (d.1.1.2 + (9 * d.1.1.1 + 5)) ∧ d.1.2 < d.1.1.1)
    (fun _ _ => 0) :=
  FibonacciHeap.Native.realizes_insert.reindex
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => ![d.1.1.1, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)

private theorem decrease_realizes : Realizes .exact
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => decreaseWord d.1.1 d.1.2 d.2)
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
    (fun w d s => FibonacciHeap.Native.decreaseValid w
      ![d.1.1.1, d.1.1.2, d.1.2, d.2] s) (fun _ _ => 0) :=
  FibonacciHeap.Native.realizes_decreaseKey.reindex
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => ![d.1.1.1, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)

private abbrev TargetArgs := (((ℕ × ℕ) × Block) × ℕ) × (ℕ × ℕ)
private abbrev word := WordEncoding.encode (α := ℕ)
private def targetInput := appendWords
  (appendWords (appendWords (WordEncoding.encode (α := ℕ × ℕ)) blockWords) word)
  (WordEncoding.encode (α := ℕ × ℕ))

private def targetSafe (w : ℕ) (d : TargetArgs) (s : Memory.State) : Prop :=
  ∃ (hv : d.1.2 < d.1.1.1.1) (K : ℕ), Fits w K ∧ Fits w (d.1.1.1.2 + (9 * d.1.1.1.1 + 5)) ∧
    (FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).Inv s ∧
    FibonacciHeap.Inv d.1.1.1.1 K ((FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).abs s) ∧
    (Block.mk (d.1.1.2.base) (d.1.1.2.length)).Allocated s ∧ d.1.1.2.length = d.1.1.1.1 ∧
    Disjoint (FibonacciHeap.footprint d.1.1.1.1 d.1.1.1.2)
      (Block.mk (d.1.1.2.base) (d.1.1.2.length)).footprint ∧
    Fits w (d.2.1 + d.2.2 + 1) ∧
    match Dictionary.Memory.decode (s.mem (d.1.1.2.base + d.1.2)) with
    | none => IndexedMinPQ.valid K (FibonacciHeap.abs d.1.1.1.1
        ((FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).abs s)) (.insert ⟨d.1.2, hv⟩ (d.2.1 + d.2.2))
    | some old => d.2.1 + d.2.2 < old → IndexedMinPQ.valid K
        (FibonacciHeap.abs d.1.1.1.1 ((FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).abs s))
        (.decreaseKey ⟨d.1.2, hv⟩ (d.2.1 + d.2.2))

private theorem target_realizes : Realizes .exact (fun d : TargetArgs =>
    relaxTarget (insertWord d.1.1.1) (decreaseWord d.1.1.1) d.1.1.2 d.1.2 d.2.1 d.2.2)
    targetInput (WordEncoding.encode (α := Unit)) targetSafe (fun _ _ => 0) := by
  realize [insert_realizes, decrease_realizes]
  all_goals rcases h with ⟨hv, K, hK, hwindow, halloc, hI, hT, hlen, hd, hsum, hop⟩
  all_goals
    have hvT : d.1.2 < (Block.mk (d.1.1.2.base) (d.1.1.2.length)).length := by
      dsimp only
      omega
  all_goals try first
    | exact hmem.fits_of_lt_frontier (hT.lt_frontier hvT)
    | exact hsum.of_le (by omega)
    | omega
  have ha : d.1.1.2.base + d.1.2 ∈ (Block.mk (d.1.1.2.base) (d.1.1.2.length)).footprint :=
    Block.mem_footprint.mpr (Block.owns_add hvT)
  have hframe : ∀ a ∈ FibonacciHeap.footprint d.1.1.1.1 d.1.1.1.2,
      Function.update s.mem (d.1.1.2.base + d.1.2) (d.2.1 + d.2.2 + 1) a = s.mem a := by
    intro a he
    apply Function.update_of_ne
    intro h
    exact (Finset.disjoint_left.mp hd) (h ▸ he) ha
  have he := FibonacciHeap.layout_abs_congr (n := d.1.1.1.1) (base := d.1.1.1.2) (s := s)
    (s' := ⟨Function.update s.mem (d.1.1.2.base + d.1.2) (d.2.1 + d.2.2 + 1), s.frontier⟩) hframe
  have hx0 : s.mem (d.1.1.2.base + d.1.2) ≠ 0 := by assumption
  rw [Dictionary.Memory.decode_of_ne_zero hx0] at hop
  obtain ⟨⟨old, hOld, hle⟩, hkey⟩ := hop hc
  refine ⟨hwindow, halloc, ⟨d.1.2, hv⟩, K, old, rfl, hK, ?_, ?_, hle, hkey⟩
  · change FibonacciHeap.Inv d.1.1.1.1 K ((FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).abs
      ⟨Function.update s.mem (d.1.1.2.base + d.1.2) (d.2.1 + d.2.2 + 1), s.frontier⟩)
    rw [he]
    exact hI
  · change FibonacciHeap.abs d.1.1.1.1 ((FibonacciHeap.layout d.1.1.1.1 d.1.1.1.2).abs
      ⟨Function.update s.mem (d.1.1.2.base + d.1.2) (d.2.1 + d.2.2 + 1), s.frontier⟩)
      ⟨d.1.2, hv⟩ = some old
    rw [he]
    exact hOld

private theorem targetSafe_of_relax_valid (G : ListInstance) {w base : ℕ} (T : Block)
    (hn : Fits w G.n) (hK : Fits w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid T w G.n (G.n * G.maxWeight + 1))
    (s : Memory.State)
    (hf : (framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s)
    (u v : Fin G.n) (du i c : ℕ)
    (hg : AdjacencyList.step G.adj (.edge u i) = (G.adj, (v, c)))
    (hv : (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        (relaxEdge u du i)))
    (hdu : du ≤ G.n * G.maxWeight) (hc : c ≤ G.maxWeight)
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hwindow : Fits w (base + (9 * G.n + 5))) :
    targetSafe w ((((G.n, base), T), v.val), (du, c)) s := by
  have hd := hf.2.2.1
  change Disjoint (FibonacciHeap.footprint G.n base)
    (T.footprint ∪ (Memory.inputGraph G.n G.m).footprint) at hd
  refine ⟨v.isLt, G.n * G.maxWeight, hK, hwindow, hf.1.1, hf.1.2,
    hf.2.1.1, hT.length_eq, hd.mono_right Finset.subset_union_left,
    hfit.of_le (by nlinarith), ?_⟩
  exact relax_valid_queue u v du i c hg hv

private abbrev Env := ((ℕ × ℕ) × Block) × (ℕ × ℕ)
/-- The input graph layout `Memory.inputGraph e.2.1 e.2.2`, spelled out because `realize` must
compute its offsets from the live words and does not unfold `Memory.inputGraph`. -/
private abbrev envGraph (e : Env) : AdjacencyList.Memory.Layout :=
  ⟨⟨3, e.2.1 + 1⟩, ⟨e.2.1 + 4, 2 * e.2.2⟩⟩
private def envInput := appendWords
  (appendWords (WordEncoding.encode (α := ℕ × ℕ)) blockWords)
  (WordEncoding.encode (α := ℕ × ℕ))
private abbrev RelaxArgs := Env × (ℕ × ℕ × ℕ)
private def relaxInput := appendWords envInput (WordEncoding.encode (α := ℕ × ℕ × ℕ))

private def relaxSafe (w : ℕ) (d : RelaxArgs) (s : Memory.State) : Prop :=
  ∃ (G : ListInstance) (base : ℕ) (hn : Fits w G.n)
    (hK : Fits w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid d.1.1.2 w G.n (G.n * G.maxWeight + 1)) (u : Fin G.n),
    d.1.1.1 = (G.n, base) ∧ d.1.2.1 = G.n ∧ d.1.2.2 = G.m ∧ d.2.1 = u.val ∧
    (framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
    d.2.2.1 ≤ G.n * G.maxWeight ∧
    Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
    Fits w (base + (9 * G.n + 5)) ∧
    (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        (relaxEdge u d.2.2.1 d.2.2.2))

private theorem relax_realizes : Realizes .exact (fun d : RelaxArgs =>
    relaxWord (insertWord d.1.1.1) (decreaseWord d.1.1.1) d.1.1.2
      (envGraph d.1) d.1.2.1 d.2.1 d.2.2.1 d.2.2.2)
    relaxInput (WordEncoding.encode (α := Unit)) relaxSafe (fun _ _ => 0) := by
  realize [insert_realizes, decrease_realizes, target_realizes]
  all_goals
    rcases d with ⟨⟨⟨e, T⟩, n, m⟩, vcur, du, i⟩
    rcases h with ⟨G, base, hnFit, hK, hT, u, he, hn, hm, hu, hf, hdu, hfit, hwindow, hv⟩
    dsimp only [envGraph] at he hn hm hu hT hdu hv ⊢
    subst e; subst n; subst m; subst vcur
    have hA : AdjacencyList.Memory.Inv (Memory.inputGraph G.n G.m) G.adj s := hf.2.1.2.1
    have hi : i < (G.adj u).length := hv.1
    obtain ⟨hoff, hlast, htgt, hwt⟩ := Memory.inputGraph_edge hA u hi
    have hbound : s.mem (G.n + 4 + 2 * (s.mem (3 + u.val) + i)) < G.n := by
      rw [htgt]
      exact ((G.adj u)[i]).1.isLt
    first
    | have hbad : ¬s.mem (G.n + 4 + 2 * (s.mem (3 + u.val) + i)) < G.n := by assumption
      exact False.elim (hbad hbound)
    | exact hmem.frontier_fits.of_le (by omega)
    | rw [htgt, hwt]
      refine targetSafe_of_relax_valid G T hnFit hK hT s hf u ((G.adj u)[i]).1 du i
        ((G.adj u)[i]).2 (AdjacencyList.step_edge G.adj u hi) hv hdu ?_ hfit hwindow
      exact G.le_maxWeight (List.getElem_mem hi)

private abbrev ScanArgs := Env × (ℕ × ℕ)
private def scanInput := appendWords envInput (WordEncoding.encode (α := ℕ × ℕ))

private def scanSafe (w : ℕ) (d : ScanArgs) (s : Memory.State) : Prop :=
  ∃ (G : ListInstance) (base : ℕ) (hn : Fits w G.n)
    (hK : Fits w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid d.1.1.2 w G.n (G.n * G.maxWeight + 1)) (u : Fin G.n),
    d.1.1.1 = (G.n, base) ∧ d.1.2.1 = G.n ∧ d.1.2.2 = G.m ∧ d.2.1 = u.val ∧
    (framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
    d.2.2 ≤ G.n * G.maxWeight ∧
    Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
    Fits w (base + (9 * G.n + 5)) ∧
    (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        (scan u d.2.2))

private theorem scan_realizes : Realizes .exact (fun d : ScanArgs =>
    scanWord (insertWord d.1.1.1) (decreaseWord d.1.1.1) d.1.1.2 (envGraph d.1) d.1.2.1 d.2.1 d.2.2)
    scanInput (WordEncoding.encode (α := Unit)) scanSafe (fun _ _ => 0) := by
  realize [relax_realizes]
  all_goals
    rcases d with ⟨⟨⟨e, T⟩, n, m⟩, vcur, du⟩
    rcases h with ⟨G, base, hnFit, hK, hT, u, he, hn, hm, hu, hf, hdu, hfit, hwindow, hv⟩
    dsimp only [envGraph] at he hn hm hu hT hdu hv ⊢
    subst e; subst n; subst m; subst vcur
    have hA : AdjacencyList.Memory.Inv (Memory.inputGraph G.n G.m) G.adj s := hf.2.1.2.1
    obtain ⟨hoff, hnext, hsucc⟩ := Memory.inputGraph_degree hA u
    first
    | exact hmem.fits_of_lt_frontier hoff
    | exact hmem.fits_of_lt_frontier hnext
    | omega
    | intro hm
      rw [hsucc, Nat.add_sub_cancel_left] at hm ⊢
      have hbfit : Fits w (G.adj u).length := (hmem.mem_fits (3 + (u.val + 1))).of_le (by omega)
      let M := framed hnFit hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
      exact Native.scan_while_safe M.toRefinement u du (G.adj u).length _
        (fun w i s => relaxSafe w ((((G.n, base), T), G.n, G.m), u.val, du, i) s)
        (fun i => relaxWord_eq (pqMethods G.n (G.n * G.maxWeight) w base)
          (insertWord (G.n, base)) (decreaseWord (G.n, base))
          (fun v k => (FibonacciHeap.Native.link_width base w (FibonacciHeap.insert v k)).symm)
          (fun v k => (FibonacciHeap.Native.link_width base w
            (FibonacciHeap.decreaseKey G.n v k)).symm)
          T (Memory.inputGraph G.n G.m) u du i)
        (fun i s _ hinv hvalid => ⟨G, base, hnFit, hK, hT, u, rfl, rfl, rfl, rfl, hinv,
          hdu, hfit, hwindow, hvalid⟩)
        s hf hbfit (scan_valid_remainingEdges u du hv) hm

private def extractWord (e : ℕ × ℕ) : Memory.Prog (Option (ℕ × ℕ)) :=
  link ((FibonacciHeap.layout e.1 e.2).methods 0) (FibonacciHeap.Native.extractRaw e.1)

private theorem extract_realizes : Realizes .exact extractWord
    (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Option (ℕ × ℕ)))
    (fun w d s => FibonacciHeap.Native.extractValid w ![d.1, d.2] s) (fun _ _ => 0) :=
  FibonacciHeap.Native.realizes_extractRaw.reindex (fun d : ℕ × ℕ => ![d.1, d.2])
    (WordEncoding.encode (α := ℕ × ℕ)) ![0, 1] (by intro d i; fin_cases i <;> rfl)

private theorem extractWord_eq (n K w base : ℕ) :
    extractWord (n, base) =
      (pqMethods n K w base .extractMin).map (Option.map fun p => (p.1.val, p.2)) := by
  simp only [extractWord, pqMethods, FibonacciHeap.methods,
    FibonacciHeap.Native.link_extractRaw_eq, FibonacciHeap.Native.link_width]
  rfl

private abbrev StepArgs := Env × ℕ
private def stepInput := appendWords envInput word

private def loopSafe (w : ℕ) (d : StepArgs) (s : Memory.State) : Prop :=
  ∃ (G : ListInstance) (base : ℕ) (hn : Fits w G.n)
    (hK : Fits w (G.n * G.maxWeight))
    (hT : Dictionary.Memory.Valid d.1.1.2 w G.n (G.n * G.maxWeight + 1)),
    d.1.1.1 = (G.n, base) ∧ d.1.2.1 = G.n ∧ d.1.2.2 = G.m ∧
    (framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
    (∀ v k, ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s).1 v =
      some k → k ≤ G.n * G.maxWeight) ∧
    Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
    Fits w (base + (9 * G.n + 5)) ∧
    (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
      ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
      ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
        ((framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        (loop d.2))

private theorem loop_realizes : Realizes .exact (fun d : StepArgs =>
    loopWord (extractWord d.1.1.1) (insertWord d.1.1.1) (decreaseWord d.1.1.1)
      d.1.1.2 (envGraph d.1) d.1.2.1 d.2)
    stepInput (WordEncoding.encode (α := Unit)) loopSafe (fun _ _ => 0) := by
  realize [scan_realizes, extract_realizes]
  rcases d with ⟨⟨⟨e, T⟩, n, m⟩, a₀⟩
  rcases h with ⟨G, base, hnFit, hK, hT, he, hn, hm, hf, hb, hfit, hwindow, hv⟩
  dsimp only [envGraph] at he hn hm hT hb hv ⊢
  subst e; subst n; subst m
  let M := framed hnFit hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
  have heq (a : ℕ) : loopStepWord (extractWord (G.n, base)) (insertWord (G.n, base))
      (decreaseWord (G.n, base)) T (Memory.inputGraph G.n G.m) G.n ((), a) =
      link M.methods (abstractLoopStep a) :=
    (loopStepWord_eq_of_erasure (pqMethods G.n (G.n * G.maxWeight) w base) _ _ _
      (fun v k => (FibonacciHeap.Native.link_width base w (FibonacciHeap.insert v k)).symm)
      (fun v k => (FibonacciHeap.Native.link_width base w
        (FibonacciHeap.decreaseKey G.n v k)).symm)
      (extractWord_eq G.n (G.n * G.maxWeight) w base) T (Memory.inputGraph G.n G.m)
      ((), a)).trans (loopStep_eq_link M.methods a)
  intro hm
  apply loop_while_safe M.toRefinement () (fun _ a => a ≠ 0) _ _
    (fun _ => Nat.pos_iff_ne_zero.symm) heq
    (fun a s => loopStepWord_result_le _ _ _ T (Memory.inputGraph G.n G.m) G.n ((), a) s)
    ?_ a₀ s hf hb hv hm
  intro a s ha hinv hkeys hvalid
  refine ⟨⟨hwindow, hinv.1.1, G.n * G.maxWeight, hK, hinv.1.2⟩, ?_⟩
  dsimp only
  rcases abstractLoopStep_extract M.toRefinement (extractWord (G.n, base))
    (extractWord_eq G.n (G.n * G.maxWeight) w base) s hinv hkeys hvalid with
    hnone | ⟨u, du, hsome, hdu, hinv', hscan⟩
  · simp [hnone]
  · rw [hsome]
    change if (1 : ℕ) = 0 then True else if u.val < G.n then _ else True
    rw [ite_eq_right (by decide), ite_eq_left u.isLt]
    exact ⟨⟨G, base, hnFit, hK, hT, u, rfl, rfl, rfl, rfl, hinv', hdu, hfit, hwindow,
      hscan⟩, ha⟩

private theorem initial_loop_safe (G : ListInstance) {w : ℕ}
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    let f := (Memory.State.init G.encode).frontier
    loopSafe w (((((G.n, f + G.n), ⟨f, G.n⟩), G.n, G.m), G.n))
      ((Memory.spec 0).clientState
        ⟨Function.update (Memory.State.init G.encode).mem (f + G.source.val) 1,
          f + G.n + (9 * G.n + 5)⟩
        (insertWord (G.n, f + G.n) G.source.val 0)) := by
  let f := (Memory.State.init G.encode).frontier
  let T : Block := ⟨f, G.n⟩
  let base := f + G.n
  have hn : Fits w G.n := hfit.of_le (by nlinarith)
  have hK : Fits w (G.n * G.maxWeight) := hfit.of_le (by nlinarith)
  have hT : Dictionary.Memory.Valid T w G.n (G.n * G.maxWeight + 1) :=
    ⟨rfl, hfit.of_le (by nlinarith)⟩
  have hwindow : Fits w (base + (9 * G.n + 5)) := hfit.of_le (by
    dsimp only [base, f]; rw [Memory.frontier_init G]; nlinarith)
  let M := framed hn hK base hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
  let s₀ : Memory.State := ⟨(Memory.State.init G.encode).mem, base + (9 * G.n + 5)⟩
  obtain ⟨hi, habs⟩ := inv_input G hn hK hT ⟨rfl⟩ hwindow
  obtain ⟨hinv, hkeys, hvalid⟩ :=
    initial_loop_safe_insert G le_rfl (by omega) M.toRefinement
      (insertWord (G.n, base) G.source.val 0) rfl
      (FibonacciHeap.Native.link_width base w (FibonacciHeap.insert G.source.val 0))
      s₀ hi habs
  exact ⟨G, base, hn, hK, hT, rfl, rfl, rfl, hinv, hkeys, hfit, hwindow, hvalid⟩

private def allocProgram (n : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let base ← Memory.allocDirty (9 * n + 5)
  pure (n, base)

private theorem alloc_realizes : Realizes .exact allocProgram word
    (WordEncoding.encode (α := ℕ × ℕ))
    (fun w n s => Fits w (s.frontier + (9 * n + 5))) (fun _ _ => 0) := by
  have hAlloc := FibonacciHeap.Native.Initialize.realizes_reserve
  unfold allocProgram
  realize
  exact h

private theorem allocProgram_run (n : ℕ) (s : Memory.State) :
    (Memory.spec 0).runClient s (allocProgram n) =
      ((n, s.frontier), ⟨s.mem, s.frontier + (9 * n + 5)⟩,
        [.allocDirty (9 * n + 5)]) := rfl

private theorem word_run_realizes : Realizes .exact
    (fun _ : Unit => runWord allocProgram extractWord insertWord decreaseWord)
    (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))
    (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) (fun _ _ => 0) := by
  unfold runWord Memory.inputGraph
  realize [alloc_realizes, insert_realizes, decrease_realizes, loop_realizes]
  case hsafe.left =>
    rcases h with ⟨G, rfl, hfit⟩
    exact hfit.of_le (by nlinarith)
  case hsafe.right.left =>
    rcases h with ⟨G, rfl, hfit⟩
    exact hfit.of_le (by nlinarith)
  case hsafe.right.right.left =>
    rcases h with ⟨G, rfl, hfit⟩
    change Fits w (G.n + 3)
    exact hfit.of_le (by nlinarith)
  case hsafe.right.right.right.left =>
    rcases h with ⟨G, rfl, hfit⟩
    change Fits w ((Memory.State.init G.encode).frontier + G.n + (9 * G.n + 5))
    rw [Memory.frontier_init]
    exact hfit.of_le (by nlinarith)
  case hsafe.right.right.right.right.isTrue.left.left =>
    rcases h with ⟨G, rfl, hfit⟩
    change Fits w ((Memory.State.init G.encode).frontier + G.source.val)
    rw [Memory.frontier_init]
    exact hfit.of_le (by have hs := G.source.isLt; nlinarith)
  case hsafe.right.right.right.right.isTrue.left.right =>
    rcases h with ⟨G, rfl, hfit⟩
    exact hfit.of_le (by nlinarith)
  case hsafe.right.right.right.right.isTrue.right.left.left =>
    rcases h with ⟨G, rfl, hfit⟩
    simp only [StateTransitionSpec.clientResult, allocProgram_run]
    change Fits w ((Memory.State.init G.encode).frontier + G.n + (9 * G.n + 5))
    rw [Memory.frontier_init]
    exact hfit.of_le (by nlinarith)
  case hsafe.right.right.right.right.isTrue.right.left.right =>
    rcases h with ⟨G, rfl, hfit⟩
    simp only [StateTransitionSpec.clientResult, allocProgram_run]
    exact G.source.isLt
  case hsafe.right.right.right.right.isTrue.right.right =>
    rcases h with ⟨G, rfl, hfit⟩
    have hn : (Memory.State.init G.encode).mem 1 = G.n := rfl
    have hs : (Memory.State.init G.encode).mem 2 = G.source.val := rfl
    have ht : (Memory.spec 0).runClient (Memory.State.init G.encode)
        (Memory.allocBlockDirty G.n) =
        (⟨(Memory.State.init G.encode).frontier, G.n⟩,
          ⟨(Memory.State.init G.encode).mem, (Memory.State.init G.encode).frontier + G.n⟩,
          [.allocDirty G.n]) := rfl
    simp only [StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      allocProgram_run, hn, hs, Memory.init_mem_edgeCount G, ht]
    exact initial_loop_safe G hfit

/-- One native emitter realizes the original Fibonacci-heap Dijkstra memory client. Its
domain retains the unchanged graph encoding and word envelope. Arithmetic, argument delivery,
dirty allocation and early-exit loop control are included in the uniform instruction factor. -/
theorem realizes_run : Realizes .exact (fun _ : Unit => run)
    (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))
    (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) (fun _ _ => 0) :=
  word_run_realizes.congr fun _ => runWord_eq

/-- One flat exact-basis program, chosen before all graphs and widths, computes every distance
within the sharper reachable-vertex Fibonacci bound. Its actual prefix, memory client and halt
are charged, and its entire final memory/frontier is the original memory client's final state.
As in the statement specification, placing the raw graph words in `Data.init` is uncharged. -/
theorem exists_program_state :
    ∃ r C pc : ℕ, ∃ prog : Program .exact r, ∃ frontier : Fin r,
      ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
        ∃ (y : Data r) (steps : ℕ), Runs w prog (State.init G.encode) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt 0 ∧
          memoryState frontier y =
            (Memory.spec w).clientState (Memory.State.init G.encode) run ∧
          steps + 1 ≤ C * (G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1)) ∧
          ∀ v : Fin G.n, y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  obtain ⟨r, C, pc, prog, frontier, he⟩ := Native.exists_program_state
    (fun G => 400 * (G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1))) realizes_run run_spec
  refine ⟨r, 401 * C, pc, prog, frontier, fun G w hfit => ?_⟩
  obtain ⟨y, steps, hrun, hhalt, hstate, htime, hdist⟩ := he G w hfit
  refine ⟨y, steps, hrun, hhalt, hstate, ?_, hdist⟩
  -- The bound is positive, since the source is a vertex.
  have hn : 1 ≤ G.n := by have := G.source.isLt; omega
  have hmin : 1 ≤ min G.n (G.m + 1) := le_min hn (by omega)
  have hpos : 1 ≤ G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1) := by
    have := Nat.mul_le_mul hmin (show 1 ≤ Nat.log 2 G.n + 1 by omega)
    omega
  nlinarith [Nat.mul_le_mul_left C hpos]

end Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci
