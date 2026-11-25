/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Domain
public import CslibFrontier.Computability.WordRAM.Realization.Structure
import CslibFrontier.Algorithms.WordRAM.Dijkstra.ListEncode
import CslibFrontier.Computability.WordRAM.Realization.LoopCongr
import CslibFrontier.Tactic.Realize

/-!
# Shared native `IndexedMinPQ` realization kernel for Dijkstra's algorithm

Both the binary-heap and Fibonacci-heap native Dijkstra endpoints execute the exact same word-level
relaxation (`relaxTarget`, `relaxWord`), out-edge scan (`scanWord`), early-exit main loop
(`loopWord`), and header/allocation entry (`runWord`) from `Dijkstra.Native.Word`. They differ
only in the priority queue's runtime register layout, framed memory refinement, dirty allocator,
and uniform `Realizes` certificates for `insert`, `decreaseKey` and erased `extractMin`.

`NativeMethods` packages a priority queue's explicit register layout encoding
`handleWords : Handle ↪ (Fin width → ℕ)`, framed refinement `framed`, and method certificates,
without hidden `WordEncoding` defaults or fixed-width specialization. Its per-stage argument
bundles (`UpdateArgs`, `TargetData`, `RelaxData`, `ScanData`, `StepData`) are named structures
encoded with `word_enc_structure`. `NativeAllocator` extends `NativeMethods` with a dirty
reservation primitive in the graph input's zero tail to yield `realizes_runWord`.

## Main definitions

* `UpdateArgs`, `updateArgsWords`: vertex and key words passed to `insert` and `decreaseKey`.
* `TargetData`, `targetDataWords`: table, target vertex, source distance and weight for one
  relaxation.
* `RelaxData`, `relaxDataWords`: graph/table context and edge coordinates for `relaxWord`.
* `ScanData`, `scanDataWords`: graph/table context and source vertex/distance for `scanWord`.
* `StepData`, `stepDataWords`: graph/table context and remaining round count for `loopWord`.
* `NativeMethods`: heap-parametric native `IndexedMinPQ` method bundle and certificates.
* `NativeMethods.dijkstraFramed`: composite framed refinement pairing the heap with the distance
  table and input adjacency arrays.
* `NativeAllocator`: dirty-allocation bundle for `runWord` on `ListInstance.encode`.

## Main results

* `NativeMethods.target_realizes`: uniform native realization of `relaxTarget`.
* `NativeMethods.relax_realizes`: uniform native realization of `relaxWord`.
* `NativeMethods.scan_realizes`: uniform native realization of `scanWord`.
* `NativeMethods.loop_realizes`: uniform native realization of `loopWord`.
* `NativeAllocator.realizes_runWord`: uniform native realization of `runWord`.
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.Dijkstra (ListInstance)

/-! ### `word_enc_structure` argument records -/

/-- Vertex handle word and tentative distance key passed to `insert` or `decreaseKey`. -/
structure UpdateArgs where
  /-- Target vertex index. -/
  vertex : ℕ
  /-- Tentative distance key. -/
  key : ℕ

/-- Faithful two-word encoding of `UpdateArgs`. -/
word_enc_structure updateArgsWords : UpdateArgs where
  vertex : wordWords,
  key : wordWords

/-- Distance table, target vertex, source distance and edge weight for `relaxTarget`. -/
structure TargetData where
  /-- Direct-address tentative-distance table. -/
  table : Block
  /-- Target vertex index. -/
  vertex : ℕ
  /-- Distance of the current source vertex. -/
  dist : ℕ
  /-- Edge weight. -/
  weight : ℕ

/-- Faithful five-word encoding of `TargetData`. -/
word_enc_structure targetDataWords : TargetData where
  table : blockWords,
  vertex : wordWords,
  dist : wordWords,
  weight : wordWords

/-- Table, graph dimensions and edge coordinates for `relaxWord`. -/
structure RelaxData where
  /-- Direct-address tentative-distance table. -/
  table : Block
  /-- Vertex count of the input graph. -/
  n : ℕ
  /-- Edge count of the input graph. -/
  m : ℕ
  /-- Source vertex index. -/
  vertex : ℕ
  /-- Distance of `vertex`. -/
  dist : ℕ
  /-- Outgoing edge offset index from `vertex`. -/
  edge : ℕ

/-- Faithful seven-word encoding of `RelaxData`. -/
word_enc_structure relaxDataWords : RelaxData where
  table : blockWords,
  n : wordWords,
  m : wordWords,
  vertex : wordWords,
  dist : wordWords,
  edge : wordWords

/-- Table, graph dimensions and extracted vertex/distance for `scanWord`. -/
structure ScanData where
  /-- Direct-address tentative-distance table. -/
  table : Block
  /-- Vertex count of the input graph. -/
  n : ℕ
  /-- Edge count of the input graph. -/
  m : ℕ
  /-- Extracted vertex index. -/
  vertex : ℕ
  /-- Extracted vertex distance. -/
  dist : ℕ

/-- Faithful six-word encoding of `ScanData`. -/
word_enc_structure scanDataWords : ScanData where
  table : blockWords,
  n : wordWords,
  m : wordWords,
  vertex : wordWords,
  dist : wordWords

/-- Table, graph dimensions and remaining round budget for `loopWord`. -/
structure StepData where
  /-- Direct-address tentative-distance table. -/
  table : Block
  /-- Vertex count of the input graph. -/
  n : ℕ
  /-- Edge count of the input graph. -/
  m : ℕ
  /-- Remaining extraction rounds. -/
  rounds : ℕ

/-- Faithful five-word encoding of `StepData`. -/
word_enc_structure stepDataWords : StepData where
  table : blockWords,
  n : wordWords,
  m : wordWords,
  rounds : wordWords

private structure HeaderData where
  n : ℕ
  src : ℕ
  m : ℕ
  table : Block

private word_enc_structure headerDataWords : HeaderData where
  n : wordWords,
  src : wordWords,
  m : wordWords,
  table : blockWords

/-! ### Left-handle polymorphic realization combinators -/

section Combinators

variable {ε : Type} {k : ℕ} (env : ε ↪ (Fin k → ℕ))

private theorem liftRight {α β : Type} {m l : ℕ}
    {p : α → Memory.Prog β} {input : α ↪ (Fin m → ℕ)} {output : β ↪ (Fin l → ℕ)}
    {safe : ℕ → α → Memory.State → Prop}
    (hp : Realizes .exact p input output safe (fun _ _ => 0)) :
    Realizes .exact (fun d : ε × α => p d.2) (appendWords env input) output
      (fun w d s => safe w d.2 s) (fun _ _ => 0) :=
  hp.reindex Prod.snd (appendWords env input) (Fin.natAdd k)
    (fun d i => (appendWords_natAdd env input d i).symm)

private theorem reindexRight {α γ β : Type} {m m' l : ℕ}
    (input : α ↪ (Fin m → ℕ))
    {q : ε × γ → Memory.Prog β} {argWords : γ ↪ (Fin m' → ℕ)}
    {output : β ↪ (Fin l → ℕ)}
    {safe : ℕ → ε × γ → Memory.State → Prop}
    (hq : Realizes .exact q (appendWords env argWords) output safe (fun _ _ => 0))
    (f : α → γ) (ix : Fin m' → Fin m)
    (hw : ∀ a i, argWords (f a) i = input a (ix i)) :
    Realizes .exact (fun d : ε × α => q (d.1, f d.2)) (appendWords env input) output
      (fun w d s => safe w (d.1, f d.2) s) (fun _ _ => 0) :=
  hq.reindex (fun d => (d.1, f d.2)) (appendWords env input)
    (Fin.addCases (Fin.castAdd m) (fun i => Fin.natAdd k (ix i)))
    (fun d => Fin.addCases
      (fun i => by simp only [Fin.addCases_left, appendWords_castAdd])
      (fun i => by simp only [Fin.addCases_right, appendWords_natAdd, hw d.2 i]))

private def assocIx (k m l : ℕ) : Fin (k + (m + l)) → Fin ((k + m) + l) :=
  Fin.addCases (fun i => Fin.castAdd l (Fin.castAdd m i))
    (Fin.addCases (fun j => Fin.castAdd l (Fin.natAdd k j)) (Fin.natAdd (k + m)))

private theorem assocIx_spec {α β : Type} {m l : ℕ}
    (input : α ↪ (Fin m → ℕ)) (answer : β ↪ (Fin l → ℕ))
    (x : (ε × α) × β) (idx : Fin (k + (m + l))) :
    appendWords env (appendWords input answer) (x.1.1, (x.1.2, x.2)) idx =
      appendWords (appendWords env input) answer x (assocIx k m l idx) := by
  refine Fin.addCases (fun i => ?_) (Fin.addCases (fun j => ?_) (fun r => ?_)) idx
  · simp only [assocIx, Fin.addCases_left, appendWords_castAdd]
  · simp only [assocIx, Fin.addCases_right, Fin.addCases_left, appendWords_natAdd,
      appendWords_castAdd]
  · simp only [assocIx, Fin.addCases_right, appendWords_natAdd]

private theorem bindRight {α β γ : Type} {m l n : ℕ}
    {p : ε × α → Memory.Prog β} {q : ε × (α × β) → Memory.Prog γ}
    {input : α ↪ (Fin m → ℕ)} {answer : β ↪ (Fin l → ℕ)} {output : γ ↪ (Fin n → ℕ)}
    {safeP : ℕ → ε × α → Memory.State → Prop}
    {safeQ : ℕ → ε × (α × β) → Memory.State → Prop}
    (hp : Realizes .exact p (appendWords env input) answer safeP (fun _ _ => 0))
    (hq : Realizes .exact q (appendWords env (appendWords input answer)) output safeQ
      (fun _ _ => 0)) :
    Realizes .exact (fun d : ε × α => (p d).bind fun b => q (d.1, (d.2, b)))
      (appendWords env input) output
      (fun w d s => safeP w d s ∧
        safeQ w (d.1, (d.2, (Memory.spec 0).clientResult s (p d)))
          ((Memory.spec 0).clientState s (p d)))
      (fun _ _ => 0) :=
  hp.bind₀ (hq.reindex (fun x : (ε × α) × β => (x.1.1, (x.1.2, x.2)))
    (appendWords (appendWords env input) answer) (assocIx k m l)
    (assocIx_spec env input answer))

private theorem branchRight {α β : Type} {m l : ℕ}
    {input : α ↪ (Fin m → ℕ)} {output : β ↪ (Fin l → ℕ)}
    (cond : Cond (k + m)) (P : α → Prop) [DecidablePred P]
    (hc : ∀ d : ε × α, test cond (appendWords env input d) ↔ P d.2)
    {pos neg : ε × α → Memory.Prog β}
    {safePos safeNeg : ℕ → ε × α → Memory.State → Prop}
    (hp : Realizes .exact pos (appendWords env input) output safePos (fun _ _ => 0))
    (hn : Realizes .exact neg (appendWords env input) output safeNeg (fun _ _ => 0)) :
    Realizes .exact
      (fun d : ε × α => if P d.2 then pos d else neg d)
      (appendWords env input) output
      (fun w d s => if P d.2 then safePos w d s else safeNeg w d s)
      (fun _ _ => 0) := by
  refine ((Realizes.branch₀ cond hp hn).congr
    fun d => if_ctx_congr (hc d) (fun _ => rfl) (fun _ => rfl)).consequence ?_
    (fun _ _ => le_rfl)
  intro w d s _ _ h
  by_cases hcond : P d.2
  · rw [ite_eq_left ((hc d).mpr hcond)]; simpa only [ite_eq_left hcond] using h
  · rw [ite_eq_right (mt (hc d).mp hcond)]; simpa only [ite_eq_right hcond] using h

private theorem branchRightEq {α β : Type} {m l : ℕ}
    {input : α ↪ (Fin m → ℕ)} {output : β ↪ (Fin l → ℕ)} (i j : Fin m)
    {pos neg : ε × α → Memory.Prog β}
    {safePos safeNeg : ℕ → ε × α → Memory.State → Prop}
    (hp : Realizes .exact pos (appendWords env input) output safePos (fun _ _ => 0))
    (hn : Realizes .exact neg (appendWords env input) output safeNeg (fun _ _ => 0)) :
    Realizes .exact
      (fun d : ε × α => if input d.2 i = input d.2 j then pos d else neg d)
      (appendWords env input) output
      (fun w d s => if input d.2 i = input d.2 j then safePos w d s else safeNeg w d s)
      (fun _ _ => 0) :=
  branchRight env (Cond.eq (Fin.natAdd k i) (Fin.natAdd k j))
    (fun a => input a i = input a j)
    (fun _ => by simp only [test, Cond.Holds, appendWords_natAdd]) hp hn

private theorem branchRightLt {α β : Type} {m l : ℕ}
    {input : α ↪ (Fin m → ℕ)} {output : β ↪ (Fin l → ℕ)} (i j : Fin m)
    {pos neg : ε × α → Memory.Prog β}
    {safePos safeNeg : ℕ → ε × α → Memory.State → Prop}
    (hp : Realizes .exact pos (appendWords env input) output safePos (fun _ _ => 0))
    (hn : Realizes .exact neg (appendWords env input) output safeNeg (fun _ _ => 0)) :
    Realizes .exact
      (fun d : ε × α => if input d.2 i < input d.2 j then pos d else neg d)
      (appendWords env input) output
      (fun w d s => if input d.2 i < input d.2 j then safePos w d s else safeNeg w d s)
      (fun _ _ => 0) :=
  branchRight env (Cond.lt (Fin.natAdd k i) (Fin.natAdd k j))
    (fun a => input a i < input a j)
    (fun _ => by simp only [test, Cond.Holds, appendWords_natAdd]) hp hn

private theorem whileRightLt {α : Type} {m : ℕ}
    {input : α ↪ (Fin m → ℕ)} (i j : Fin (m + 1))
    (cutoff : α × ℕ → ℕ) {body : ε × (α × ℕ) → Memory.Prog ℕ}
    {safe : ℕ → ε × (α × ℕ) → Memory.State → Prop}
    (hb : Realizes .exact body (appendWords env (appendWords input wordWords)) wordWords
      safe (fun _ _ => 0))
    (hq : ∀ x s, 1 ≤ memoryCost (body x) s) :
    Realizes .exact
      (fun d : ε × (α × ℕ) => boundedWhile
        (fun (p : ε × α) (a : ℕ) =>
          appendWords input wordWords (p.2, a) i < appendWords input wordWords (p.2, a) j)
        (fun x : (ε × α) × ℕ => body (x.1.1, (x.1.2, x.2)))
        (d.1, d.2.1) (cutoff d.2) d.2.2)
      (appendWords env (appendWords input wordWords)) wordWords
      (fun w d s =>
        whileSafe
          (fun (p : ε × α) (a : ℕ) =>
            appendWords input wordWords (p.2, a) i < appendWords input wordWords (p.2, a) j)
          (fun x : (ε × α) × ℕ => body (x.1.1, (x.1.2, x.2)))
          (fun w x s => safe w (x.1.1, (x.1.2, x.2)) s)
          w (d.1, d.2.1) (cutoff d.2) d.2.2 s)
      (fun _ _ => 0) := by
  let body' : (ε × α) × ℕ → Memory.Prog ℕ := fun x => body (x.1.1, (x.1.2, x.2))
  let mapIdx (u : Fin (m + 1)) : Fin ((k + m) + 1) :=
    Fin.addCases (fun r : Fin m => Fin.castAdd 1 (Fin.natAdd k r))
      (fun r : Fin 1 => Fin.natAdd (k + m) r) u
  have hmap (p : ε × α) (a : ℕ) (u : Fin (m + 1)) :
      appendWords (appendWords env input) wordWords (p, a) (mapIdx u) =
        appendWords input wordWords (p.2, a) u := by
    refine Fin.addCases (fun r => ?_) (fun r => ?_) u
    · simp only [mapIdx, Fin.addCases_left, appendWords_castAdd, appendWords_natAdd]
    · simp only [mapIdx, Fin.addCases_right, appendWords_natAdd]
  let cond : Cond ((k + m) + 1) := Cond.lt (mapIdx i) (mapIdx j)
  have hcond (p : ε × α) (a : ℕ) :
      test cond (appendWords (appendWords env input) wordWords (p, a)) ↔
        appendWords input wordWords (p.2, a) i < appendWords input wordWords (p.2, a) j := by
    simp only [test, Cond.Holds, cond, hmap]
  have hb' : Realizes .exact body' (appendWords (appendWords env input) wordWords) wordWords
      (fun w x s => safe w (x.1.1, (x.1.2, x.2)) s) (fun _ _ => 0) :=
    hb.reindex (fun x : (ε × α) × ℕ => (x.1.1, (x.1.2, x.2)))
      (appendWords (appendWords env input) wordWords) (assocIx k m 1)
      (assocIx_spec env input wordWords)
  have hL := Realizes.while₀ (appendWords env input) wordWords cond
    (fun x : (ε × α) × ℕ => cutoff (x.1.2, x.2)) hb' (fun x s => hq (x.1.1, (x.1.2, x.2)) s)
  have hL' := hL.reindex (fun d : ε × (α × ℕ) => ((d.1, d.2.1), d.2.2))
    (appendWords env (appendWords input wordWords))
    (Fin.addCases (Fin.addCases (Fin.castAdd (m + 1))
      (fun r : Fin m => Fin.natAdd k (Fin.castAdd 1 r)))
      (fun r : Fin 1 => Fin.natAdd k (Fin.natAdd m r)))
    (fun d => Fin.addCases
      (Fin.addCases
        (fun r => by simp only [Fin.addCases_left, appendWords_castAdd])
        (fun r => by simp only [Fin.addCases_right, Fin.addCases_left,
          appendWords_castAdd, appendWords_natAdd]))
      (fun r => by simp only [Fin.addCases_right, appendWords_natAdd]))
  refine (hL'.congr fun d => boundedWhile_congr _ _ (hcond (d.1, d.2.1))
    (fun _ => rfl) (cutoff d.2) d.2.2).consequence ?_ (fun _ _ => le_rfl)
  intro w d s _ _ h
  exact whileSafe_imp _ _ (fun a => (hcond (d.1, d.2.1) a).symm) (fun _ => rfl)
    (fun _ _ _ hs => hs) h

end Combinators

/-! ### `NativeMethods`: shared realization of `relaxTarget`, `relaxWord`, `scanWord`, `loopWord` -/

/-- A uniform native `IndexedMinPQ` method family over `Memory.Prog` for Dijkstra's algorithm,
parameterized by an explicit register layout encoding `handleWords`, static validity `Valid`, a
framed memory refinement `framed`, and zero-local-work `Realizes` certificates for `insert`,
`decreaseKey`, and handle-erased `extractMin`. -/
structure NativeMethods where
  /-- Runtime heap handle carried in registers across the client. -/
  Handle : Type
  /-- Number of register words encoding a runtime heap handle. -/
  width : ℕ
  /-- Explicit faithful register encoding of a runtime heap handle. -/
  handleWords : Handle ↪ (Fin width → ℕ)
  /-- Static handle validity predicate at word width `w`, capacity `n`, and key bound `K`. -/
  Valid : ℕ → ℕ → ℕ → Handle → Prop
  /-- Framed refinement of `indexedMinPQSpec n K` over `Memory.spec w`. -/
  framed : ∀ {w n K : ℕ} {e : Handle}, Valid w n K e →
    Memory.Framed (indexedMinPQSpec n K) w
  /-- Word-argument `insert` program. -/
  insert : Handle → ℕ → ℕ → Memory.Prog Unit
  /-- Word-argument `decreaseKey` program. -/
  decreaseKey : Handle → ℕ → ℕ → Memory.Prog Unit
  /-- Erased `extractMin` program returning `Option (ℕ × ℕ)`. -/
  extractMin : Handle → Memory.Prog (Option (ℕ × ℕ))
  /-- Typed `insert` agrees with the framed refinement's `.insert` method. -/
  insert_eq : ∀ {w n K : ℕ} {e : Handle} (hV : Valid w n K e) (v : Fin n) (k : ℕ),
    insert e v.val k = (framed hV).methods (.insert v k)
  /-- Typed `decreaseKey` agrees with the framed refinement's `.decreaseKey` method. -/
  decreaseKey_eq : ∀ {w n K : ℕ} {e : Handle} (hV : Valid w n K e) (v : Fin n) (k : ℕ),
    decreaseKey e v.val k = (framed hV).methods (.decreaseKey v k)
  /-- Erased `extractMin` agrees with handle-proof erasure of the framed `.extractMin` method. -/
  extractMin_eq : ∀ {w n K : ℕ} {e : Handle} (hV : Valid w n K e),
    extractMin e = ((framed hV).methods .extractMin).map (Option.map fun p => (p.1.val, p.2))
  /-- Every `extractMin` call charges at least one memory unit, paying main-loop control. -/
  extractMin_query : ∀ (e : Handle) (s : Memory.State), 1 ≤ memoryCost (extractMin e) s
  /-- Uniform native realization of `insert`. -/
  realizes_insert : Realizes .exact
    (fun d : Handle × UpdateArgs => insert d.1 d.2.vertex d.2.key)
    (appendWords handleWords updateArgsWords) (WordEncoding.encode (α := Unit))
    (fun w d s => ∃ (n : ℕ) (hv : d.2.vertex < n) (K : ℕ) (hV : Valid w n K d.1),
      (framed hV).inv s ∧
        IndexedMinPQ.valid K ((framed hV).abs s) (.insert ⟨d.2.vertex, hv⟩ d.2.key))
    (fun _ _ => 0)
  /-- Uniform native realization of `decreaseKey`. -/
  realizes_decreaseKey : Realizes .exact
    (fun d : Handle × UpdateArgs => decreaseKey d.1 d.2.vertex d.2.key)
    (appendWords handleWords updateArgsWords) (WordEncoding.encode (α := Unit))
    (fun w d s => ∃ (n : ℕ) (hv : d.2.vertex < n) (K : ℕ) (hV : Valid w n K d.1),
      (framed hV).inv s ∧
        IndexedMinPQ.valid K ((framed hV).abs s) (.decreaseKey ⟨d.2.vertex, hv⟩ d.2.key))
    (fun _ _ => 0)
  /-- Uniform native realization of erased `extractMin`. -/
  realizes_extractMin : Realizes .exact extractMin
    handleWords (WordEncoding.encode (α := Option (ℕ × ℕ)))
    (fun w e s => ∃ (n K : ℕ) (hV : Valid w n K e), (framed hV).inv s)
    (fun _ _ => 0)

namespace NativeMethods

variable (M : NativeMethods)

/-- Composite framed refinement of `Dijkstra.spec` pairing `M.framed hV` with the direct-address
distance table `T` and immutable adjacency arrays `A`. -/
@[expose] def dijkstraFramed {w n K V : ℕ} {e : M.Handle} (hV : M.Valid w n K e) {T : Block}
    (hT : Dictionary.Memory.Valid T w n V) {A : AdjacencyList.Memory.Layout}
    (hA : A.Valid n) (adj : AdjacencyList.State n) :
    Memory.Framed (spec n K V) w :=
  (M.framed hV).prod
    ((Dictionary.Memory.framed (n_max := n) hT).prod
      (AdjacencyList.Memory.framed adj hA))

/-- Entry domain for `relaxTarget` over `M`. -/
@[expose] def targetSafe (w : ℕ) (d : M.Handle × TargetData) (s : Memory.State) : Prop :=
  ∃ (n : ℕ) (hv : d.2.vertex < n) (K : ℕ) (hV : M.Valid w n K d.1),
    (M.framed hV).inv s ∧
      Fits w (s.frontier + (M.framed hV).room s) ∧
      d.2.table.Allocated s ∧ d.2.table.length = n ∧
      Disjoint ((M.framed hV).footprint s) d.2.table.footprint ∧
      Fits w (d.2.dist + d.2.weight + 1) ∧
      match Dictionary.Memory.decode (s.mem (d.2.table.base + d.2.vertex)) with
      | none => IndexedMinPQ.valid K ((M.framed hV).abs s)
          (.insert ⟨d.2.vertex, hv⟩ (d.2.dist + d.2.weight))
      | some old => d.2.dist + d.2.weight < old →
          IndexedMinPQ.valid K ((M.framed hV).abs s)
            (.decreaseKey ⟨d.2.vertex, hv⟩ (d.2.dist + d.2.weight))

private theorem table_write_framed {w n K v z : ℕ} {e : M.Handle} (hV : M.Valid w n K e)
    {T : Block} {s : Memory.State} (hi : (M.framed hV).inv s)
    (hroom : Fits w (s.frontier + (M.framed hV).room s))
    (hv : v < T.length) (hd : Disjoint ((M.framed hV).footprint s) T.footprint) :
    (M.framed hV).inv ⟨Function.update s.mem (T.base + v) z, s.frontier⟩ ∧
      (M.framed hV).abs ⟨Function.update s.mem (T.base + v) z, s.frontier⟩ =
        (M.framed hV).abs s := by
  have ha : T.base + v ∈ T.footprint := Block.mem_footprint.mpr (Block.owns_add hv)
  have he : ∀ a ∈ (M.framed hV).footprint s,
      Function.update s.mem (T.base + v) z a = s.mem a := fun a h =>
    Function.update_of_ne (fun hEq => Finset.disjoint_left.mp hd (hEq ▸ h) ha) _ _
  exact ((M.framed hV).congr (s' := ⟨Function.update s.mem (T.base + v) z, s.frontier⟩) hi he
    le_rfl hroom).imp_right And.left

private theorem table_write_op {w n K v z : ℕ} {e : M.Handle} (hV : M.Valid w n K e)
    {T : Block} {s : Memory.State} (hi : (M.framed hV).inv s)
    (hroom : Fits w (s.frontier + (M.framed hV).room s))
    (hv : v < n) (hlen : T.length = n)
    (hd : Disjoint ((M.framed hV).footprint s) T.footprint)
    (mkOp : ∀ {m : ℕ}, Fin m → IndexedMinPQ.Op m)
    (hop : IndexedMinPQ.valid K ((M.framed hV).abs s) (mkOp ⟨v, hv⟩)) :
    ∃ (n' : ℕ) (hv' : v < n') (K' : ℕ) (hV' : M.Valid w n' K' e),
      (M.framed hV').inv ⟨Function.update s.mem (T.base + v) z, s.frontier⟩ ∧
        IndexedMinPQ.valid K'
          ((M.framed hV').abs ⟨Function.update s.mem (T.base + v) z, s.frontier⟩)
          (mkOp ⟨v, hv'⟩) := by
  obtain ⟨hi', habs'⟩ := M.table_write_framed hV hi hroom (hlen ▸ hv) hd (z := z)
  exact ⟨n, hv, K, hV, hi', habs'.symm ▸ hop⟩

private def targetReadSum (a : TargetData) : Memory.Prog ((ℕ × ℕ) × ℕ) := do
  let x ← read (a.table.base + a.vertex)
  let d ← pure (a.dist + a.weight)
  pure ((x, 0), d)

private theorem targetReadSum_realizes : Realizes .exact targetReadSum
    targetDataWords (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
    (fun w a _ => Fits w (a.table.base + a.vertex) ∧ Fits w (a.dist + a.weight))
    (fun _ _ => 0) := by
  unfold targetReadSum
  realize
  all_goals first | exact h.1 | exact h.2

private def targetWrite (p : TargetData × ((ℕ × ℕ) × ℕ)) : Memory.Prog Unit :=
  write (p.1.table.base + p.1.vertex) (Prod.snd p.2 + 1)

private theorem targetWrite_realizes : Realizes .exact targetWrite
    (appendWords targetDataWords (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)))
    (WordEncoding.encode (α := Unit))
    (fun w p _ => Fits w (p.1.table.base + p.1.vertex) ∧ Fits w (Prod.snd p.2 + 1))
    (fun _ _ => 0) := by
  unfold targetWrite
  realize
  all_goals first | exact h.1 | exact h.2

private def targetSubOne (p : TargetData × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ :=
  pure (Prod.fst (Prod.fst p.2) - 1)

private theorem targetSubOne_realizes : Realizes .exact targetSubOne
    (appendWords targetDataWords (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))) wordWords
    (fun _ p _ => 1 ≤ Prod.fst (Prod.fst p.2))
    (fun _ _ => 0) := by
  unfold targetSubOne
  realize
  exact h

private theorem noop_realizes {α : Type} {m : ℕ} (input : α ↪ (Fin m → ℕ)) :
    Realizes .exact (fun _ : α => (pure () : Memory.Prog Unit))
      input (WordEncoding.encode (α := Unit)) (fun _ _ _ => True) (fun _ _ => 0) :=
  (show Realizes .exact (fun _ : Unit => (pure () : Memory.Prog Unit))
    (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))
    (fun _ _ _ => True) (fun _ _ => 0) by realize).reindex
      (fun _ => ()) input Fin.elim0 (fun _ i => i.elim0)

/-- Uniform native realization of `relaxTarget` for any `NativeMethods`. -/
theorem target_realizes : Realizes .exact
    (fun d : M.Handle × TargetData =>
      relaxTarget (M.insert d.1) (M.decreaseKey d.1)
        d.2.table d.2.vertex d.2.dist d.2.weight)
    (appendWords M.handleWords targetDataWords) (WordEncoding.encode (α := Unit))
    M.targetSafe (fun _ _ => 0) := by
  let enc8 := appendWords targetDataWords (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
  let enc8u := appendWords enc8 (WordEncoding.encode (α := Unit))
  let enc9 := appendWords enc8 wordWords
  let enc9u := appendWords enc9 (WordEncoding.encode (α := Unit))
  have hInsBranch := bindRight M.handleWords
    (liftRight M.handleWords targetWrite_realizes)
    (reindexRight M.handleWords enc8u M.realizes_insert
      (fun q : (TargetData × ((ℕ × ℕ) × ℕ)) × Unit => ⟨q.1.1.vertex, Prod.snd q.1.2⟩)
      ![2, 7] (by intro q i; fin_cases i <;> rfl))
  have hDecWrite := targetWrite_realizes.reindex Prod.fst enc9 (Fin.castAdd 1)
    (fun p i => (appendWords_castAdd enc8 wordWords p i).symm)
  have hDecBranch := bindRight M.handleWords
    (liftRight M.handleWords hDecWrite)
    (reindexRight M.handleWords enc9u M.realizes_decreaseKey
      (fun q : ((TargetData × ((ℕ × ℕ) × ℕ)) × ℕ) × Unit => ⟨q.1.1.1.vertex, Prod.snd q.1.1.2⟩)
      ![2, 7] (by intro q i; fin_cases i <;> rfl))
  have hInnerIf := branchRightLt M.handleWords (input := enc9) (7 : Fin 9) (8 : Fin 9)
    hDecBranch (liftRight M.handleWords (noop_realizes enc9))
  have hElseBranch := bindRight M.handleWords
    (liftRight M.handleWords targetSubOne_realizes) hInnerIf
  have hOuterIf := branchRightEq M.handleWords (input := enc8) (5 : Fin 8) (6 : Fin 8)
    hInsBranch hElseBranch
  have hFull := bindRight M.handleWords
    (liftRight M.handleWords targetReadSum_realizes) hOuterIf
  refine (hFull.congr fun d => ?_).consequence ?_ (fun _ _ => le_rfl)
  · dsimp only [targetReadSum, targetWrite, targetSubOne]
    unfold relaxTarget
    simp only [PFunctor.FreeM.bind_eq_bind, bind_assoc, pure_bind]
    congr 1 with x : 1
  · intro w d s _ hmem ⟨n, hv, K, hV, hi, hroom, hT, hlen, hd, hsum, hop⟩
    have hAddrFit : Fits w (d.2.table.base + d.2.vertex) :=
      hmem.fits_of_lt_frontier (hT.lt_frontier (hlen ▸ hv))
    refine ⟨⟨hAddrFit, hsum.of_le (by omega)⟩, ?_⟩
    change if s.mem (d.2.table.base + d.2.vertex) = 0 then _ else _
    split_ifs with hx0 hlt
    · refine ⟨⟨hAddrFit, hsum⟩, M.table_write_op hV hi hroom hv hlen hd
        (fun u => .insert u (d.2.dist + d.2.weight)) ?_⟩
      simpa only [hx0, Dictionary.Memory.decode_zero] using hop
    · rw [Dictionary.Memory.decode_of_ne_zero hx0] at hop
      exact ⟨Nat.one_le_iff_ne_zero.mpr hx0, ⟨hAddrFit, hsum⟩, M.table_write_op hV hi hroom hv
        hlen hd (fun u => .decreaseKey u (d.2.dist + d.2.weight)) (hop hlt)⟩
    · exact ⟨Nat.one_le_iff_ne_zero.mpr hx0, trivial⟩

/-- Entry domain for `relaxWord` over `M`. -/
@[expose] def relaxSafe (w : ℕ) (d : M.Handle × RelaxData) (s : Memory.State) : Prop :=
  ∃ (G : ListInstance) (hV : M.Valid w G.n (G.n * G.maxWeight) d.1)
    (hT : Dictionary.Memory.Valid d.2.table w G.n (G.n * G.maxWeight + 1))
    (u : Fin G.n),
    d.2.n = G.n ∧ d.2.m = G.m ∧ d.2.vertex = u.val ∧
      (M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
      d.2.dist ≤ G.n * G.maxWeight ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
      (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
        ((M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
          ((M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
          (relaxEdge u d.2.dist d.2.edge))

private def relaxReadEdge (a : RelaxData) : Memory.Prog ((ℕ × ℕ) × ℕ) := do
  let off ← read (3 + a.vertex)
  let t ← read ((a.n + 4) + 2 * (off + a.edge))
  let c ← read ((a.n + 4) + (2 * (off + a.edge) + 1))
  pure ((t, c), 0)

private theorem relaxReadEdge_realizes : Realizes .exact relaxReadEdge
    relaxDataWords (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
    (fun w a s =>
      Fits w (3 + a.vertex) ∧
        Fits w ((a.n + 4) + (2 * (s.mem (3 + a.vertex) + a.edge) + 1)))
    (fun _ _ => 0) := by
  unfold relaxReadEdge
  realize
  all_goals first
    | exact h.1
    | exact h.2
    | exact h.2.of_le (by omega)

/-- Uniform native realization of `relaxWord` on `Memory.inputGraph` for any `NativeMethods`. -/
theorem relax_realizes : Realizes .exact
    (fun d : M.Handle × RelaxData =>
      relaxWord (M.insert d.1) (M.decreaseKey d.1) d.2.table
        (Memory.inputGraph d.2.n d.2.m) d.2.n d.2.vertex d.2.dist d.2.edge)
    (appendWords M.handleWords relaxDataWords) (WordEncoding.encode (α := Unit))
    M.relaxSafe (fun _ _ => 0) := by
  let enc10 := appendWords relaxDataWords (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
  have hTrue := reindexRight M.handleWords enc10 M.target_realizes
    (fun p : RelaxData × ((ℕ × ℕ) × ℕ) =>
      ⟨p.1.table, Prod.fst (Prod.fst p.2), p.1.dist, Prod.snd (Prod.fst p.2)⟩)
    ![0, 1, 7, 5, 8] (by intro p i; fin_cases i <;> rfl)
  have hFalse := reindexRight M.handleWords enc10 M.target_realizes
    (fun p : RelaxData × ((ℕ × ℕ) × ℕ) => ⟨p.1.table, p.1.vertex, p.1.dist, Prod.snd p.2⟩)
    ![0, 1, 4, 5, 9] (by intro p i; fin_cases i <;> rfl)
  have hBranch := branchRightLt M.handleWords (input := enc10) (7 : Fin 10) (2 : Fin 10)
    hTrue hFalse
  have hFull := bindRight M.handleWords
    (liftRight M.handleWords relaxReadEdge_realizes) hBranch
  refine (hFull.congr fun d => ?_).consequence ?_ (fun _ _ => le_rfl)
  · dsimp only [relaxReadEdge]
    unfold relaxWord Memory.inputGraph
    simp only [PFunctor.FreeM.bind_eq_bind, bind_assoc, pure_bind]
    congr 1 with off : 1
  · intro w d s _ hmem ⟨G, hV, hT, u, hn, hm, hu, hf, hdu, hfit, hv⟩
    rcases d with ⟨e, ⟨T, n, m, vcur, du, idx⟩⟩
    dsimp only at hV hT hn hm hu hf hdu hv ⊢
    subst hn hm hu
    have hA : AdjacencyList.Memory.Inv (Memory.inputGraph G.n G.m) G.adj s := hf.2.1.2.1
    have hi : idx < (G.adj u).length := hv.1
    obtain ⟨hoff, hlast, htgt, hwt⟩ := Memory.inputGraph_edge hA u hi
    refine ⟨⟨hmem.fits_of_lt_frontier hoff, hmem.fits_of_lt_frontier hlast⟩, ?_⟩
    have hRes : (Memory.spec 0).clientResult s (relaxReadEdge ⟨T, G.n, G.m, u.val, du, idx⟩) =
        ((((G.adj u)[idx]).1.val, ((G.adj u)[idx]).2), 0) := by
      change ((s.mem _, s.mem _), 0) = _; rw [htgt, hwt]
    have hSt : (Memory.spec 0).clientState s (relaxReadEdge ⟨T, G.n, G.m, u.val, du, idx⟩) =
        s := rfl
    rw [hRes, hSt]
    change if ((G.adj u)[idx]).1.val < G.n then _ else _
    rw [ite_eq_left ((G.adj u)[idx]).1.isLt]
    have hdApart : Disjoint ((M.framed hV).footprint s)
        (T.footprint ∪ (Memory.inputGraph G.n G.m).footprint) := hf.2.2.1
    have hroomApart : Fits w (s.frontier + (M.framed hV).room s) :=
      hf.2.2.2.of_le (by omega)
    have hcBound : ((G.adj u)[idx]).2 ≤ G.maxWeight := G.le_maxWeight (List.getElem_mem hi)
    refine ⟨G.n, ((G.adj u)[idx]).1.isLt, G.n * G.maxWeight, hV, hf.1, hroomApart,
      hf.2.1.1, hT.length_eq, hdApart.mono_right Finset.subset_union_left,
      hfit.of_le (by
        dsimp only
        have := Nat.mul_le_mul_right (G.maxWeight + 2) (by omega : G.n + 1 ≤ 8 * (G.n + G.m + 2))
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_add] at this; omega), ?_⟩
    exact relax_valid_queue u ((G.adj u)[idx]).1 du idx ((G.adj u)[idx]).2
      (AdjacencyList.step_edge G.adj u hi) hv

/-- Entry domain for `scanWord` over `M`. -/
@[expose] def scanSafe (w : ℕ) (d : M.Handle × ScanData) (s : Memory.State) : Prop :=
  ∃ (G : ListInstance) (hV : M.Valid w G.n (G.n * G.maxWeight) d.1)
    (hT : Dictionary.Memory.Valid d.2.table w G.n (G.n * G.maxWeight + 1))
    (u : Fin G.n),
    d.2.n = G.n ∧ d.2.m = G.m ∧ d.2.vertex = u.val ∧
      (M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
      d.2.dist ≤ G.n * G.maxWeight ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
      (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
        ((M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
          ((M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
          (scan u d.2.dist))

private def scanReadDegree (a : ScanData) : Memory.Prog (ℕ × ℕ) := do
  let x ← read (3 + a.vertex)
  let y ← read (3 + (a.vertex + 1))
  let deg ← pure (y - x)
  pure (deg, 0)

private theorem scanReadDegree_realizes : Realizes .exact scanReadDegree
    scanDataWords (WordEncoding.encode (α := ℕ × ℕ))
    (fun w a s =>
      Fits w (3 + a.vertex) ∧ Fits w (3 + (a.vertex + 1)) ∧
        s.mem (3 + a.vertex) ≤ s.mem (3 + (a.vertex + 1)))
    (fun _ _ => 0) := by
  unfold scanReadDegree
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2

private def scanInc (x : (ScanData × ℕ) × ℕ) : Memory.Prog ℕ :=
  pure (x.2 + 1)

private theorem scanInc_realizes : Realizes .exact scanInc
    (appendWords (appendWords scanDataWords wordWords) wordWords) wordWords
    (fun w x _ => Fits w (x.2 + 1))
    (fun _ _ => 0) := by
  unfold scanInc
  realize
  exact h

/-- Uniform native realization of `scanWord` on `Memory.inputGraph` for any `NativeMethods`. -/
theorem scan_realizes : Realizes .exact
    (fun d : M.Handle × ScanData =>
      scanWord (M.insert d.1) (M.decreaseKey d.1) d.2.table
        (Memory.inputGraph d.2.n d.2.m) d.2.n d.2.vertex d.2.dist)
    (appendWords M.handleWords scanDataWords) (WordEncoding.encode (α := Unit))
    M.scanSafe (fun _ _ => 0) := by
  let enc7 := appendWords scanDataWords wordWords
  let enc8 := appendWords enc7 wordWords
  let enc8u := appendWords enc8 (WordEncoding.encode (α := Unit))
  have hInc := scanInc_realizes.reindex
    (fun y : ((ScanData × ℕ) × ℕ) × Unit => y.1) enc8u (Fin.castAdd 0)
    (fun y i => (appendWords_castAdd enc8 (WordEncoding.encode (α := Unit)) y i).symm)
  have hStep := bindRight M.handleWords
    (reindexRight M.handleWords enc8 M.relax_realizes
      (fun x : (ScanData × ℕ) × ℕ =>
        ⟨x.1.1.table, x.1.1.n, x.1.1.m, x.1.1.vertex, x.1.1.dist, x.2⟩)
      ![0, 1, 2, 3, 4, 5, 7] (by intro x i; fin_cases i <;> rfl))
    (liftRight M.handleWords hInc)
  have hWhile := whileRightLt M.handleWords (input := enc7) (7 : Fin 8) (6 : Fin 8)
    (fun q : (ScanData × ℕ) × ℕ => q.1.2) hStep
    (fun x s => one_le_memoryCost_liftBind (.read (3 + x.2.1.1.vertex)) _ s)
  have hWhileReindexed := reindexRight M.handleWords
    (appendWords scanDataWords (WordEncoding.encode (α := ℕ × ℕ)))
    hWhile (fun q : ScanData × (ℕ × ℕ) => ((q.1, q.2.1), q.2.2))
    ![0, 1, 2, 3, 4, 5, 6, 7] (by intro q i; fin_cases i <;> rfl)
  have hAfterWhile := bindRight M.handleWords hWhileReindexed
    (liftRight M.handleWords (noop_realizes
      (appendWords (appendWords scanDataWords (WordEncoding.encode (α := ℕ × ℕ))) wordWords)))
  have hFull := bindRight M.handleWords
    (liftRight M.handleWords scanReadDegree_realizes) hAfterWhile
  refine (hFull.congr fun d => ?_).consequence_valid ?_
  · dsimp only [scanReadDegree]
    unfold scanWord Memory.inputGraph
    simp only [PFunctor.FreeM.bind_eq_bind, bind_assoc, pure_bind]
    congr 1 with x : 1
    congr 1 with y : 1
    exact congrArg (fun p => p >>= fun _ => pure ())
      (boundedWhile_congr
        (fun (p : M.Handle × (ScanData × ℕ)) (a : ℕ) => enc8 (p.2, a) 7 < enc8 (p.2, a) 6)
        (fun (b : ℕ) (i : ℕ) => i < b)
        (fun _ => Iff.rfl) (fun _ => rfl) (y - x) 0)
  · intro w d s _ hmem hvHist ⟨G, hV, hT, u, hn, hm, hu, hf, hdu, hfit, hv⟩
    rcases d with ⟨e, ⟨T, n, m, vcur, du⟩⟩
    dsimp only at hV hT hn hm hu hf hdu hv hvHist ⊢
    subst hn hm hu
    have hA : AdjacencyList.Memory.Inv (Memory.inputGraph G.n G.m) G.adj s := hf.2.1.2.1
    obtain ⟨hoff, hnext, hsucc⟩ := Memory.inputGraph_degree hA u
    have hdegEq : s.mem (3 + (u.val + 1)) - s.mem (3 + u.val) = (G.adj u).length := by omega
    refine ⟨⟨hmem.fits_of_lt_frontier hoff, hmem.fits_of_lt_frontier hnext, by omega⟩, ?_,
      trivial⟩
    have hDegRes : (Memory.spec 0).clientResult s (scanReadDegree ⟨T, G.n, G.m, u.val, du⟩) =
        ((G.adj u).length, 0) := by
      change (s.mem (3 + (u.val + 1)) - s.mem (3 + u.val), 0) = _; rw [hdegEq]
    have hDegSt : (Memory.spec 0).clientState s (scanReadDegree ⟨T, G.n, G.m, u.val, du⟩) =
        s := rfl
    rw [hDegRes, hDegSt]
    have hbfit : Fits w (G.adj u).length :=
      (hmem.mem_fits (3 + (u.val + 1))).of_le (by omega)
    let D := M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
    have hv2 : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (boundedWhile (fun b i : ℕ => i < b) (fun x => do
          relaxWord (M.insert e) (M.decreaseKey e) T (Memory.inputGraph G.n G.m)
            G.n u.val du x.2
          pure (x.2 + 1)) (s.mem (3 + (u.val + 1)) - s.mem (3 + u.val))
            (s.mem (3 + (u.val + 1)) - s.mem (3 + u.val)) 0 >>= fun _ => pure ())) := hvHist.2.2
    rw [hdegEq] at hv2
    have hws := Native.scan_while_safe D.toRefinement u du (G.adj u).length
      (fun idx => relaxWord (M.insert e) (M.decreaseKey e) T (Memory.inputGraph G.n G.m)
        G.n u.val du idx)
      (fun w idx s => M.relaxSafe w (e, ⟨T, G.n, G.m, u.val, du, idx⟩) s)
      (fun idx => relaxWord_eq (M.framed hV).methods (M.insert e) (M.decreaseKey e)
        (M.insert_eq hV) (M.decreaseKey_eq hV) T (Memory.inputGraph G.n G.m) u du idx)
      (fun idx s _ hinv hvalid => ⟨G, hV, hT, u, rfl, rfl, rfl, hinv, hdu, hfit, hvalid⟩)
      s hf hbfit (scan_valid_remainingEdges u du hv) (((validHistory_bind' ..).mp hv2).1)
    exact whileSafe_imp
      (fun (b : ℕ) (i : ℕ) => i < b)
      (fun (p : M.Handle × (ScanData × ℕ)) (a : ℕ) => enc8 (p.2, a) 7 < enc8 (p.2, a) 6)
      (fun _ => Iff.rfl) (fun _ => rfl) (fun _ _ _ hs => hs) hws

/-- Entry domain for `loopWord` over `M`. -/
@[expose] def loopSafe (w : ℕ) (d : M.Handle × StepData) (s : Memory.State) : Prop :=
  ∃ (G : ListInstance) (hV : M.Valid w G.n (G.n * G.maxWeight) d.1)
    (hT : Dictionary.Memory.Valid d.2.table w G.n (G.n * G.maxWeight + 1)),
    d.2.n = G.n ∧ d.2.m = G.m ∧
      (M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).inv s ∧
      (∀ v k, (M.framed hV).abs s v = some k → k ≤ G.n * G.maxWeight) ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) ∧
      (spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).ValidHistory
        ((M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
        ((spec G.n (G.n * G.maxWeight) (G.n * G.maxWeight + 1)).clientHistory
          ((M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj).abs s)
          (loop d.2.rounds))

private def stepInit (a : StepData) : Memory.Prog (ℕ × ℕ) :=
  pure (0, a.rounds)

private theorem stepInit_realizes : Realizes .exact stepInit
    stepDataWords (WordEncoding.encode (α := ℕ × ℕ))
    (fun _ _ _ => True) (fun _ _ => 0) := by
  unfold stepInit
  realize

private theorem pureZero_realizes {α : Type} {m : ℕ} (input : α ↪ (Fin m → ℕ)) :
    Realizes .exact (fun _ : α => (pure 0 : Memory.Prog ℕ))
      input wordWords (fun _ _ _ => True) (fun _ _ => 0) :=
  (show Realizes .exact (fun _ : Unit => (pure 0 : Memory.Prog ℕ))
    (WordEncoding.encode (α := Unit)) wordWords (fun _ _ _ => True) (fun _ _ => 0) by realize)
    |>.reindex (fun _ => ()) input Fin.elim0 (fun _ i => i.elim0)

private def stepDec (x : (((StepData × ℕ) × ℕ) × Option (ℕ × ℕ)) × Unit) : Memory.Prog ℕ :=
  pure (x.1.1.2 - 1)

private theorem stepDec_realizes : Realizes .exact stepDec
    (appendWords
      (appendWords (appendWords (appendWords stepDataWords wordWords) wordWords)
        (WordEncoding.encode (α := Option (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit)))
    wordWords
    (fun _ x _ => 1 ≤ x.1.1.2)
    (fun _ _ => 0) := by
  unfold stepDec
  realize
  exact h

/-- Uniform native realization of `loopWord` on `Memory.inputGraph` for any `NativeMethods`. -/
theorem loop_realizes : Realizes .exact
    (fun d : M.Handle × StepData =>
      loopWord (M.extractMin d.1) (M.insert d.1) (M.decreaseKey d.1) d.2.table
        (Memory.inputGraph d.2.n d.2.m) d.2.n d.2.rounds)
    (appendWords M.handleWords stepDataWords) (WordEncoding.encode (α := Unit))
    M.loopSafe (fun _ _ => 0) := by
  let enc6 := appendWords stepDataWords wordWords
  let enc7 := appendWords enc6 wordWords
  let enc10 := appendWords enc7 (WordEncoding.encode (α := Option (ℕ × ℕ)))
  have hExtract := M.realizes_extractMin.reindex
    (fun x : M.Handle × ((StepData × ℕ) × ℕ) => x.1) (appendWords M.handleWords enc7)
    (Fin.castAdd 7) (fun x i => (appendWords_castAdd M.handleWords enc7 x i).symm)
  have hScanDec := bindRight M.handleWords
    (reindexRight M.handleWords enc10 M.scan_realizes
      (fun y : ((StepData × ℕ) × ℕ) × Option (ℕ × ℕ) =>
        ⟨y.1.1.1.table, y.1.1.1.n, y.1.1.1.m, enc10 y 8, enc10 y 9⟩)
      ![0, 1, 2, 3, 8, 9] (by intro y i; fin_cases i <;> rfl))
    (liftRight M.handleWords stepDec_realizes)
  have hInnerIf := branchRightLt M.handleWords (input := enc10) (8 : Fin 10) (2 : Fin 10)
    hScanDec (liftRight M.handleWords (pureZero_realizes enc10))
  have hOuterIf := branchRightEq M.handleWords (input := enc10) (7 : Fin 10) (5 : Fin 10)
    (liftRight M.handleWords (pureZero_realizes enc10)) hInnerIf
  have hBodyRaw := bindRight M.handleWords hExtract hOuterIf
  have hBodyEq (x : M.Handle × ((StepData × ℕ) × ℕ)) (hzero : x.2.1.2 = 0) :
      ((M.extractMin x.1).bind fun opt =>
        if enc10 (x.2, opt) 7 = enc10 (x.2, opt) 5 then pure 0
        else if enc10 (x.2, opt) 8 < enc10 (x.2, opt) 2 then
          (scanWord (M.insert x.1) (M.decreaseKey x.1) x.2.1.1.table
            (Memory.inputGraph x.2.1.1.n x.2.1.1.m) x.2.1.1.n
            (enc10 (x.2, opt) 8) (enc10 (x.2, opt) 9)).bind fun _ => pure (x.2.2 - 1)
        else pure 0) =
      loopStepWord (M.extractMin x.1) (M.insert x.1) (M.decreaseKey x.1)
        x.2.1.1.table (Memory.inputGraph x.2.1.1.n x.2.1.1.m) x.2.1.1.n ((), x.2.2) := by
    unfold loopStepWord
    simp only [PFunctor.FreeM.bind_eq_bind]
    congr 1 with opt : 1
    rcases opt with _ | ⟨u, du⟩
    · exact ite_eq_left hzero.symm
    · change (if 1 = x.2.1.2 then _ else _) = _
      rw [hzero, ite_eq_right (by decide)]; rfl
  have hWhile := whileRightLt M.handleWords (input := enc6) (5 : Fin 7) (6 : Fin 7)
    (fun q : (StepData × ℕ) × ℕ => q.1.1.rounds) hBodyRaw
    (fun x s => by rw [memoryCost_bind]; have := M.extractMin_query x.1 s; omega)
  have hWhileReindexed := reindexRight M.handleWords
    (appendWords stepDataWords (WordEncoding.encode (α := ℕ × ℕ))) hWhile
    (fun q : StepData × (ℕ × ℕ) => ((q.1, q.2.1), q.2.2))
    ![0, 1, 2, 3, 4, 5, 6] (by intro q i; fin_cases i <;> rfl)
  have hAfterWhile := bindRight M.handleWords hWhileReindexed
    (liftRight M.handleWords (noop_realizes
      (appendWords (appendWords stepDataWords (WordEncoding.encode (α := ℕ × ℕ))) wordWords)))
  have hFull := bindRight M.handleWords
    (liftRight M.handleWords stepInit_realizes) hAfterWhile
  refine (hFull.congr fun d => ?_).consequence_valid ?_
  · dsimp only [stepInit]
    unfold loopWord Memory.inputGraph
    simp only [PFunctor.FreeM.bind_eq_bind, pure_bind]
    exact congrArg (fun p => p >>= fun _ => pure ())
      (boundedWhile_congr
        (fun (p : M.Handle × (StepData × ℕ)) (a : ℕ) => enc7 (p.2, a) 5 < enc7 (p.2, a) 6)
        (fun (_ : Unit) (a : ℕ) => a ≠ 0)
        (fun _ => Nat.pos_iff_ne_zero)
        (fun a => hBodyEq (d.1, ((d.2, 0), a)) rfl) d.2.rounds d.2.rounds)
  · intro w d s _ _ hvHist ⟨G, hV, hT, hn, hm, hf, hb, hfit, hv⟩
    rcases d with ⟨e, ⟨T, n, m, a0⟩⟩
    dsimp only at hV hT hn hm hf hb hv hvHist ⊢
    subst hn hm
    refine ⟨trivial, ?_, trivial⟩
    let D := M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
    have heqStep (a : ℕ) : loopStepWord (M.extractMin e) (M.insert e) (M.decreaseKey e) T
        (Memory.inputGraph G.n G.m) G.n ((), a) = link D.methods (abstractLoopStep a) :=
      (loopStepWord_eq_of_erasure (K := G.n * G.maxWeight) (V := G.n * G.maxWeight + 1)
        (M.framed hV).methods (M.extractMin e) (M.insert e) (M.decreaseKey e)
        (M.insert_eq hV) (M.decreaseKey_eq hV) (M.extractMin_eq hV)
        T (Memory.inputGraph G.n G.m) ((), a)).trans (loopStep_eq_link D.methods a)
    unfold loopWord at hvHist
    have hws := loop_while_safe D.toRefinement () (fun _ a => a ≠ 0)
      (loopStepWord (M.extractMin e) (M.insert e) (M.decreaseKey e)
        T (Memory.inputGraph G.n G.m) G.n)
      (fun w x s =>
        (∃ (n' K : ℕ) (hV' : M.Valid w n' K e), (M.framed hV').inv s) ∧
        let opt := (Memory.spec 0).clientResult s (M.extractMin e)
        let s' := (Memory.spec 0).clientState s (M.extractMin e)
        if enc10 (((⟨T, G.n, G.m, a0⟩, 0), x.2), opt) 7 = 0 then True
        else if enc10 (((⟨T, G.n, G.m, a0⟩, 0), x.2), opt) 8 < G.n then
          M.scanSafe w (e, ⟨T, G.n, G.m,
            enc10 (((⟨T, G.n, G.m, a0⟩, 0), x.2), opt) 8,
            enc10 (((⟨T, G.n, G.m, a0⟩, 0), x.2), opt) 9⟩) s' ∧ 1 ≤ x.2
        else True)
      (fun _ => Nat.pos_iff_ne_zero.symm) heqStep
      (fun a s => loopStepWord_result_le _ _ _ T (Memory.inputGraph G.n G.m) G.n ((), a) s)
      (fun a s ha hinv hkeys hvalid => by
        refine ⟨⟨G.n, G.n * G.maxWeight, hV, hinv.1⟩, ?_⟩
        rcases abstractLoopStep_extract D.toRefinement (M.extractMin e) (M.extractMin_eq hV)
          s hinv hkeys hvalid with hnone | ⟨u, du, hsome, hdu, hinv', hscan⟩
        · dsimp only; rw [hnone]; exact ite_eq_left rfl ▸ trivial
        · dsimp only; rw [hsome]
          have h7 : enc10 (((⟨T, G.n, G.m, a0⟩, 0), a), some (u.val, du)) 7 = 1 := rfl
          have h8 : enc10 (((⟨T, G.n, G.m, a0⟩, 0), a), some (u.val, du)) 8 = u.val := rfl
          rw [h7, ite_eq_right (by decide), h8, ite_eq_left u.isLt]
          exact ⟨⟨G, hV, hT, u, rfl, rfl, rfl, hinv', hdu, hfit, hscan⟩, ha⟩)
      a0 s hf hb hv (((validHistory_bind' ..).mp hvHist).1)
    exact whileSafe_imp
      (fun (_ : Unit) (a : ℕ) => a ≠ 0)
      (fun (p : M.Handle × (StepData × ℕ)) (a : ℕ) => enc7 (p.2, a) 5 < enc7 (p.2, a) 6)
      (fun _ => Nat.pos_iff_ne_zero.symm)
      (fun a => (hBodyEq (e, ((⟨T, G.n, G.m, a0⟩, 0), a)) rfl).symm)
      (fun _ _ _ hs => hs) hws

end NativeMethods

/-! ### `NativeAllocator`: shared realization of `runWord` -/

/-- Dirty-allocation extension of `NativeMethods` for `Dijkstra.Native.runWord` on the standard
graph input encoding `ListInstance.encode`. -/
structure NativeAllocator (M : NativeMethods) where
  /-- Allocate an empty priority queue of capacity `n` in dirty memory at the current frontier. -/
  alloc : ℕ → Memory.Prog M.Handle
  /-- Number of dirty cells reserved by `alloc n`. -/
  span : ℕ → ℕ
  /-- Handle value returned by `alloc n` starting from frontier `b`. -/
  allocated : ℕ → ℕ → M.Handle
  /-- Deterministic memory-oracle result and frontier advance of `alloc n`. -/
  run_alloc : ∀ n (s : Memory.State),
    (Memory.spec 0).clientResult s (alloc n) = allocated n s.frontier ∧
      (Memory.spec 0).clientState s (alloc n) = ⟨s.mem, s.frontier + span n⟩
  /-- Uniform native realization of `alloc`. -/
  realizes_alloc : Realizes .exact alloc wordWords M.handleWords
    (fun w n s => Fits w (s.frontier + span n)) (fun _ _ => 0)
  /-- Under Dijkstra's standard word-size envelope `Fits w (8 (n + m + 2) (W + 2))`, reserving the
  distance table (`G.n` cells) and heap (`span G.n` cells) fits in `w` bits. -/
  fits_alloc : ∀ (G : ListInstance) {w : ℕ},
    Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
      Fits w ((Memory.State.init G.encode).frontier + G.n + span G.n)
  /-- Under Dijkstra's word-size envelope, the allocated handle is statically valid at capacity
  `G.n` for keys up to `G.n * G.maxWeight`, represents an empty queue in the zero tail past
  `f + G.n`, and keeps its footprint at or above `f + G.n` with zero room. -/
  init_empty : ∀ (G : ListInstance) {w : ℕ},
    Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
    let f := (Memory.State.init G.encode).frontier
    let e := allocated G.n (f + G.n)
    let s : Memory.State := ⟨(Memory.State.init G.encode).mem, f + G.n + span G.n⟩
    ∃ (hV : M.Valid w G.n (G.n * G.maxWeight) e),
      (M.framed hV).inv s ∧
      (∀ v, (M.framed hV).abs s v = none) ∧
      (M.framed hV).room s = 0 ∧
      ∀ a ∈ (M.framed hV).footprint s, f + G.n ≤ a

namespace NativeAllocator

variable {M : NativeMethods} (A : NativeAllocator M)

private def readGraphHeader (_ : Unit) : Memory.Prog HeaderData := do
  let n ← read 1
  let src ← read 2
  let m ← read (n + 3)
  let T ← allocBlockDirty n
  pure ⟨n, src, m, T⟩

private theorem readGraphHeader_realizes : Realizes .exact readGraphHeader
    (WordEncoding.encode (α := Unit)) headerDataWords
    (fun w _ s => Fits w 1 ∧ Fits w 2 ∧ Fits w (s.mem 1 + 3))
    (fun _ _ => 0) := by
  unfold readGraphHeader Memory.allocBlockDirty
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2

private def initSourceDist (h : HeaderData) : Memory.Prog ℕ := do
  let z ← pure 0
  write (h.table.base + h.src) (z + 1)
  pure z

private theorem initSourceDist_realizes : Realizes .exact initSourceDist
    headerDataWords wordWords
    (fun w h _ => Fits w (h.table.base + h.src) ∧ Fits w 1)
    (fun _ _ => 0) := by
  unfold initSourceDist
  realize
  all_goals first | exact h.1 | exact h.2

/-- Uniform native realization of `runWord A.alloc M.extractMin M.insert M.decreaseKey`. -/
theorem realizes_runWord : Realizes .exact
    (fun _ : Unit => runWord A.alloc M.extractMin M.insert M.decreaseKey)
    (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))
    (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (fun _ _ => 0) := by
  let enc05 := appendWords (WordEncoding.encode (α := Unit)) headerDataWords
  let hdrWithZero := appendWords headerDataWords wordWords
  let hdrWithZeroUnit := appendWords hdrWithZero (WordEncoding.encode (α := Unit))
  have hAllocCall := A.realizes_alloc.reindex
    (fun u : Unit × HeaderData => u.2.n) enc05 ![0] (by intro u i; fin_cases i; rfl)
  have hClientCont := bindRight M.handleWords
    (reindexRight M.handleWords hdrWithZero M.realizes_insert
      (fun p : HeaderData × ℕ => ⟨p.1.src, p.2⟩) ![1, 5]
      (by intro p i; fin_cases i <;> rfl))
    (reindexRight M.handleWords hdrWithZeroUnit M.loop_realizes
      (fun q : (HeaderData × ℕ) × Unit => ⟨q.1.1.table, q.1.1.n, q.1.1.m, q.1.1.n⟩)
      ![3, 4, 0, 2, 0] (by intro q i; fin_cases i <;> rfl))
  have hClient := bindRight M.handleWords
    (liftRight M.handleWords initSourceDist_realizes) hClientCont
  have hIfSrc := branchRightLt M.handleWords (input := headerDataWords) (1 : Fin 5) (0 : Fin 5)
    hClient (liftRight M.handleWords (NativeMethods.noop_realizes headerDataWords))
  have hIfSrcReindexed := hIfSrc.reindex
    (fun x : (Unit × HeaderData) × M.Handle => (x.2, x.1.2))
    (appendWords enc05 M.handleWords)
    (Fin.addCases (Fin.natAdd 5) (Fin.castAdd M.width))
    (fun x => Fin.addCases
      (fun i => by
        rw [Fin.addCases_left, appendWords_castAdd]
        exact (appendWords_natAdd enc05 M.handleWords x i).symm)
      (fun j => by
        rw [Fin.addCases_right, appendWords_natAdd, appendWords_castAdd enc05 M.handleWords x j]
        fin_cases j <;> rfl))
  have hFull := readGraphHeader_realizes.bind₀ (hAllocCall.bind₀ hIfSrcReindexed)
  refine (hFull.congr fun _ => ?_).consequence ?_ (fun _ _ => le_rfl)
  · dsimp only [readGraphHeader, initSourceDist]
    unfold runWord clientWord Memory.allocBlockDirty
    simp only [PFunctor.FreeM.bind_eq_bind, bind_assoc, pure_bind]
    congr 1 with n : 1
  · rintro w _ _ _ _ ⟨G, rfl, hfit⟩
    have hbase : 8 * (G.n + G.m + 2) ≤ 8 * (G.n + G.m + 2) * (G.maxWeight + 2) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hm3 : (Memory.State.init G.encode).mem (G.n + 3) = G.m := Memory.init_mem_edgeCount G
    refine ⟨⟨hfit.of_le (by omega), hfit.of_le (by omega),
      hfit.of_le (show (Memory.State.init G.encode).mem 1 + 3 ≤ _ by change G.n + 3 ≤ _; omega)⟩,
      ?_⟩
    have hHdrRes : (Memory.spec 0).clientResult (Memory.State.init G.encode)
        (readGraphHeader ()) =
        ⟨G.n, G.source.val, G.m, ⟨(Memory.State.init G.encode).frontier, G.n⟩⟩ := by
      rw [← hm3]; rfl
    have hHdrSt : (Memory.spec 0).clientState (Memory.State.init G.encode)
        (readGraphHeader ()) =
        ⟨(Memory.State.init G.encode).mem, (Memory.State.init G.encode).frontier + G.n⟩ := rfl
    rw [hHdrRes, hHdrSt]
    refine ⟨A.fits_alloc G hfit, ?_⟩
    obtain ⟨hAllocRes, hAllocSt⟩ := A.run_alloc G.n
      ⟨(Memory.State.init G.encode).mem, (Memory.State.init G.encode).frontier + G.n⟩
    rw [hAllocRes, hAllocSt]
    dsimp only
    change if G.source.val < G.n then _ else _
    rw [ite_eq_left G.source.isLt]
    refine ⟨⟨by
        rw [Memory.frontier_init G]
        exact hfit.of_le (by have := G.source.isLt; omega),
      hfit.of_le (by omega)⟩, ?_⟩
    obtain ⟨hV, hInvEmpty, hAbsEmpty, hRoomZero, hFpAbove⟩ := A.init_empty G hfit
    let f := (Memory.State.init G.encode).frontier
    let e0 := A.allocated G.n (f + G.n)
    let sAlloc : Memory.State := ⟨(Memory.State.init G.encode).mem, f + G.n + A.span G.n⟩
    let sWrite : Memory.State :=
      ⟨Function.update (Memory.State.init G.encode).mem (f + G.source.val) 1,
        f + G.n + A.span G.n⟩
    have hInitRes : (Memory.spec 0).clientResult sAlloc
        (initSourceDist ⟨G.n, G.source.val, G.m, ⟨f, G.n⟩⟩) = 0 := rfl
    have hInitSt : (Memory.spec 0).clientState sAlloc
        (initSourceDist ⟨G.n, G.source.val, G.m, ⟨f, G.n⟩⟩) = sWrite := rfl
    rw [hInitRes, hInitSt]
    have hFrameWrite : ∀ a ∈ (M.framed hV).footprint sAlloc, sWrite.mem a = sAlloc.mem a :=
      fun a ha => Function.update_of_ne
        (by have hlo : f + G.n ≤ a := hFpAbove a ha; have := G.source.isLt; omega) _ _
    have hRoomFit : Fits w (sWrite.frontier + (M.framed hV).room sAlloc) := by
      dsimp only [sWrite, f]; rw [hRoomZero, Nat.add_zero]; exact A.fits_alloc G hfit
    obtain ⟨hInvWrite, hAbsWrite, -⟩ := (M.framed hV).congr (s' := sWrite) hInvEmpty
      hFrameWrite le_rfl hRoomFit
    refine ⟨⟨G.n, G.source.isLt, G.n * G.maxWeight, hV, hInvWrite, ?_⟩, ?_⟩
    · change (M.framed hV).abs sWrite G.source = none ∧ 0 ≤ G.n * G.maxWeight
      exact ⟨hAbsWrite ▸ hAbsEmpty _, Nat.zero_le _⟩
    · have hT : Dictionary.Memory.Valid ⟨f, G.n⟩ w G.n (G.n * G.maxWeight + 1) :=
        ⟨rfl, hfit.of_le (by
          have := Nat.mul_le_mul_right (G.maxWeight + 2) (by omega : G.n + 1 ≤ 8 * (G.n + G.m + 2))
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_add] at this; omega)⟩
      let D := M.dijkstraFramed hV hT (A := Memory.inputGraph G.n G.m) ⟨rfl⟩ G.adj
      obtain ⟨hTAinv, hTAabs, hTAlt⟩ := Memory.inv_tableGraph G hT ⟨rfl⟩ (by omega)
        (A.fits_alloc G hfit)
      have hDisj : Disjoint ((M.framed hV).footprint sAlloc)
          (((Dictionary.Memory.framed (n_max := G.n) hT).prod
            (AdjacencyList.Memory.framed (L := Memory.inputGraph G.n G.m)
              G.adj ⟨rfl⟩)).footprint sAlloc) :=
        Finset.disjoint_left.mpr fun a ha hb =>
          by have := hFpAbove a ha; have := hTAlt _ a hb; omega
      have hApartFit : Fits w (sAlloc.frontier + ((M.framed hV).room sAlloc + (0 + 0))) := by
        dsimp only [sAlloc, f]; rw [hRoomZero]; simpa using A.fits_alloc G hfit
      have hLoopSafe := initial_loop_safe_insert G le_rfl (by omega) D.toRefinement
        (M.insert e0 G.source.val 0) rfl (M.insert_eq hV G.source 0).symm
        sAlloc ⟨hInvEmpty, hTAinv, hDisj, hApartFit⟩ (Prod.ext (funext hAbsEmpty) hTAabs)
      exact ⟨G, hV, hT, rfl, rfl, hLoopSafe.1, hLoopSafe.2.1, hfit, hLoopSafe.2.2⟩

end NativeAllocator

end Cslib.Algorithms.Lean.Dijkstra.Native
