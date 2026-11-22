/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.BudgetAsymptotics
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.Bridge
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameAccessors
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactClocked

/-!
# The block network as an edge network, read by terms

For a machine, an input `x`, a clock `t` and a schedule `σ`, the block-counting network
`blockNetworkOf machine e (x, t, σ)` is rows-first bipartite with its first
`numBlocks t * (3k + 2)` vertices as rows (`RowsFirst`), and then
`blockEdgeNet machine e p x t σ hd = EdgeNet.ofExplicit (ZMod p) _ _ hd` is an edge network on its
vertices. This file identifies the parts of that edge network with the numeric descriptions of
Complexitylib and with the terms of the old route, so the new route can read the network without
storing it.

## The parts on numbers

* `M_blockEdgeNet`, `length_vertices`: `edgesN k s t` edges and `verticesN k s t` vertices.
* `map_val_ports`, `length_ports`, `val_get_ports`: the ports of a vertex are `netPorts k s t σ v`
  (`explicitPortsNum`), in order.
* `val_u`, `val_w`: the ends of edge `i` are `explicitSrcNum … i` (the row) and
  `explicitTgtNum … i` (the column).
* `val_eval`, `val_eval_ofFn`: the table of `v` at bits `bs` of the right length is the entry
  `tableEntryNum … (lsbValue bs)` reduced mod `p`.
* `nodup_ports`, `length_ports_le_maxDegree`, `length_ports_le`: port lists are duplicate free and
  of length at most the maximum degree (at most `C ⌊log₂ t⌋` for an admissible network).

## The terms

From a term `τT` for the clock, `nT` for the input length and `σT` for the schedule:
`clkEdgesT` (edges), `clkVerticesT` (vertices), `edgeUT`/`edgeWT` (ends), `clkArityT` (degree),
`clkPortT` (ports) and `evalAtT` (tables mod `p`), built from `clkBlockLenT`, `clkNumBlocksT` and
`clkRadixT`. Each has a `denote_*` lemma stating its value is the quantity of `blockEdgeNet` at the
clock `t` denoted by `τT`, and a `StableAt` lemma. `tm_clkAccessors` (the clock-generic form of the
old route's `tm_accessors`), `tm_netTerms` and `tm_ends1` give their tiers.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.NetTerm

open ProgTerm ProgTerm.Term LocalSim _root_.Turing _root_.Turing.MultiTapePTM Budget
    Cslib.Complexity.CountingSimulation Cslib.Circuits.Frontier

variable {k s : ℕ} {State : Type} [DecidableEq State] (machine : MultiTapePTM k Bool State)
  (e : State ≃ Fin s)

/-- The block network of `(x, t, σ)` is rows-first bipartite with its row count. -/
abbrev RowsFirst (x : List Bool) (t σ : ℕ) : Prop :=
  (blockNetworkOf machine e (x, t, σ)).2.IsRowsFirstBipartite (blockNetworkOf machine e (x, t, σ)).1

/-- The block network of `(x, t, σ)` as an edge network over `ZMod p`. -/
noncomputable abbrev blockEdgeNet (p : ℕ) (x : List Bool) (t σ : ℕ) (hd : RowsFirst machine e x t σ)
    :
    EdgeNet (ZMod p) (Fin (blockNetworkOf machine e (x, t, σ)).2.vertices.length) :=
  EdgeNet.ofExplicit (ZMod p) _ _ hd

/-! ### The parts on numbers -/

section Facts

variable {machine e} {p : ℕ} {x : List Bool} {t σ : ℕ}

theorem length_vertices :
    (blockNetworkOf machine e (x, t, σ)).2.vertices.length = verticesN k s t :=
  length_vertices_blockNetworkOf machine e x t σ

omit [DecidableEq State] in
theorem rows_eq : (blockNetworkOf machine e (x, t, σ)).1 = numBlocks t * (3 * k + 2) := rfl

/-- Vertex `v`: its ports `netPorts` and its table of entries `tableEntryNum`. -/
theorem vertex_eq (v : ℕ) (hv : v < (blockNetworkOf machine e (x, t, σ)).2.vertices.length) :
    (blockNetworkOf machine e (x, t, σ)).2.vertices[v] =
      (netPorts k s t σ v, (List.range (2 ^ (netPorts k s t σ v).length)).map
        (tableEntryNum e (blockLength t) machine x (numBlocks t) σ v (netPorts k s t σ v))) := by
  have h := vertex_blockNetworkOf machine e x t σ v (by rwa [length_vertices_blockNetworkOf] at hv)
  rw [List.getElem?_eq_getElem hv] at h
  exact Option.some.inj h

theorem vertex_fst (v : ℕ) (hv : v < (blockNetworkOf machine e (x, t, σ)).2.vertices.length) :
    ((blockNetworkOf machine e (x, t, σ)).2.vertices[v]).1 = netPorts k s t σ v := by
  rw [vertex_eq v hv]

variable (hd : RowsFirst machine e x t σ)

theorem M_blockEdgeNet : (blockEdgeNet machine e p x t σ hd).M = edgesN k s t :=
  numEdges_blockNetworkOf machine e x t σ

omit [DecidableEq State] in
theorem ports_blockEdgeNet (v : Fin (blockNetworkOf machine e (x, t, σ)).2.vertices.length) :
    (blockEdgeNet machine e p x t σ hd).ports v = EdgeNet.portsOf _ _ hd v := rfl

/-- The ports of `v`, as numbers, are `netPorts k s t σ v`. -/
theorem map_val_ports (v : Fin (blockNetworkOf machine e (x, t, σ)).2.vertices.length) :
    ((blockEdgeNet machine e p x t σ hd).ports v).map Fin.val = netPorts k s t σ v := by
  show (EdgeNet.portsOf (blockNetworkOf machine e (x, t, σ)).2 _ hd v).map Fin.val = _
  rw [EdgeNet.portsOf, List.map_pmap]
  simp only [List.pmap_eq_map, List.map_id']
  exact vertex_fst v.1 v.2

/-- The degree of `v`. -/
theorem length_ports (v : Fin (blockNetworkOf machine e (x, t, σ)).2.vertices.length) :
    ((blockEdgeNet machine e p x t σ hd).ports v).length = (netPorts k s t σ v).length := by
  rw [← map_val_ports hd v, List.length_map]

/-- The `j`-th port of `v`. -/
theorem val_get_ports (v : Fin (blockNetworkOf machine e (x, t, σ)).2.vertices.length)
    (j : Fin ((blockEdgeNet machine e p x t σ hd).ports v).length) :
    (((blockEdgeNet machine e p x t σ hd).ports v).get j : ℕ) = (netPorts k s t σ v).getD j 0 := by
  have hj : j.1 < (netPorts k s t σ v).length := length_ports hd v ▸ j.2
  rw [List.getD_eq_getElem _ _ hj]
  have h : (((blockEdgeNet machine e p x t σ hd).ports v).map Fin.val)[j.1]'(by simp) =
      (netPorts k s t σ v)[j.1] := List.getElem_of_eq (map_val_ports hd v) _
  simpa using h

omit [DecidableEq State] in
/-- No edge is a port of a vertex twice. -/
theorem nodup_ports (v : Fin (blockNetworkOf machine e (x, t, σ)).2.vertices.length) :
    ((blockEdgeNet machine e p x t σ hd).ports v).Nodup :=
  EdgeNet.nodup_ports_ofDescribed _ _ hd _ v

theorem le_foldr_max : ∀ (l : List (List ℕ × List ℕ)) (j : ℕ) (hj : j < l.length),
    l[j].1.length ≤ (l.map fun v => v.1.length).foldr max 0
  | [], j, hj => absurd hj (by simp)
  | a :: l, 0, _ => by simp
  | a :: l, j + 1, hj => by
    simp only [List.getElem_cons_succ, List.map_cons, List.foldr_cons]
    exact (le_foldr_max l j (by simpa using hj)).trans (le_max_right _ _)

omit [DecidableEq State] in
/-- The degree is at most the maximum degree. -/
theorem length_ports_le_maxDegree (v : Fin (blockNetworkOf machine e (x, t, σ)).2.vertices.length) :
    ((blockEdgeNet machine e p x t σ hd).ports v).length ≤
      (blockNetworkOf machine e (x, t, σ)).2.maxDegree := by
  show (EdgeNet.portsOf (blockNetworkOf machine e (x, t, σ)).2 _ hd v).length ≤ _
  rw [EdgeNet.portsOf, List.length_pmap]
  exact le_foldr_max _ _ v.2

omit [DecidableEq State] in
/-- The degree of an admissible network is at most `C ⌊log₂ t⌋`. -/
theorem length_ports_le {C t' : ℕ} (hadm : ExplicitAdmissible C t'
    (blockNetworkOf machine e (x, t, σ)))
    (v : Fin (blockNetworkOf machine e (x, t, σ)).2.vertices.length) :
    ((blockEdgeNet machine e p x t σ hd).ports v).length ≤ C * Nat.log 2 t' :=
  (length_ports_le_maxDegree hd v).trans hadm.2.2.1

/-- The row end of edge `i` is its source `explicitSrcNum`. -/
theorem val_u (i : Fin (blockEdgeNet machine e p x t σ hd).M) :
    ((blockEdgeNet machine e p x t σ hd).u i : ℕ) =
      explicitSrcNum k (numBlocks t) (letterBits k s (blockLength t)) σ i := by
  obtain ⟨hr, hmem⟩ := EdgeNet.rowOf_spec (blockNetworkOf machine e (x, t, σ)).2 _ hd i
  change (EdgeNet.rowOf _ _ hd i : ℕ) = _
  have hr' : (EdgeNet.rowOf _ _ hd i : ℕ) < numBlocks t * (3 * k + 2) := hr
  rw [vertex_fst _ (EdgeNet.rowOf _ _ hd i).2] at hmem
  unfold netPorts explicitPortsNum at hmem
  have h := (List.mem_filter.1 hmem).2
  simp only [decide_eq_true_eq] at h
  rcases h with h | h
  · exact h.symm
  · unfold explicitTgtNum at h; omega

/-- The column end of edge `i` is its target `explicitTgtNum`. -/
theorem val_w (i : Fin (blockEdgeNet machine e p x t σ hd).M) :
    ((blockEdgeNet machine e p x t σ hd).w i : ℕ) =
      explicitTgtNum k (numBlocks t) (letterBits k s (blockLength t)) i := by
  have hi : (i : ℕ) < edgesN k s t := M_blockEdgeNet (p := p) hd ▸ i.2
  set T := explicitTgtNum k (numBlocks t) (letterBits k s (blockLength t)) i with hT
  have hTlt : T < (blockNetworkOf machine e (x, t, σ)).2.vertices.length := by
    rw [length_vertices, hT]; unfold explicitTgtNum verticesN; unfold edgesN at hi
    split_ifs <;> omega
  have hTr : ¬ T < (blockNetworkOf machine e (x, t, σ)).1 := by
    rw [rows_eq, hT]; unfold explicitTgtNum; omega
  have hmem : (i : ℕ) ∈ ((blockNetworkOf machine e (x, t, σ)).2.vertices[T]).1 := by
    rw [vertex_fst _ hTlt]
    unfold netPorts explicitPortsNum
    exact List.mem_filter.2 ⟨List.mem_range.2 hi, by simp [hT]⟩
  have := EdgeNet.col_unique _ _ hd i.2 (j := EdgeNet.colOf _ _ hd i) (j' := ⟨T, hTlt⟩)
    (EdgeNet.colOf_spec _ _ hd i).1 hTr (EdgeNet.colOf_spec _ _ hd i).2 hmem
  exact congrArg Fin.val this

/-- The table of `v` at bits of the right length, mod `p`. -/
theorem val_eval (v : Fin (blockNetworkOf machine e (x, t, σ)).2.vertices.length) (bs : List Bool)
    (hbs : bs.length = ((blockEdgeNet machine e p x t σ hd).ports v).length) :
    ((blockEdgeNet machine e p x t σ hd).eval v bs).val =
      tableEntryNum e (blockLength t) machine x (numBlocks t) σ v (netPorts k s t σ v)
        (Cslib.BitString.lsbValue bs) % p := by
  change (((ExplicitTensorNetwork.entry
    ((blockNetworkOf machine e (x, t, σ)).2.vertices[v.1]).2 bs : ℕ) : ZMod p)).val = _
  rw [ZMod.val_natCast, vertex_eq v.1 v.2, ExplicitTensorNetwork.entry]
  have hlt : Cslib.BitString.lsbValue bs < 2 ^ (netPorts k s t σ v).length := by
    have := Cslib.BitString.lsbValue_lt bs
    rwa [hbs, length_ports hd v] at this
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range]

/-- The table of `v` at the bits of a number `A` (bit `j` on the `j`-th port), mod `p`. -/
theorem val_eval_ofFn (v : Fin (blockNetworkOf machine e (x, t, σ)).2.vertices.length) (A : ℕ) :
    ((blockEdgeNet machine e p x t σ hd).eval v
        (List.ofFn fun j : Fin ((blockEdgeNet machine e p x t σ hd).ports
            v).length => A.testBit j)).val =
      tableEntryNum e (blockLength t) machine x (numBlocks t) σ v (netPorts k s t σ v)
        (A % 2 ^ (netPorts k s t σ v).length) % p := by
  rw [val_eval hd v _ (List.length_ofFn), lsbValue_ofFn_testBit, length_ports hd v]

end Facts

/-! ### The terms -/

section Terms

variable (k s)

/-- The block length `blockLength τ` at the clock `τT`. -/
def clkBlockLenT (τT : Term) : Term := clogT (add τT (const 2))

/-- The number of blocks `numBlocks τ` at the clock `τT`. -/
def clkNumBlocksT (τT : Term) : Term := ceilDivT τT (clkBlockLenT τT)

/-- The number of edges `edgesN k s τ`. -/
def clkEdgesT (τT : Term) : Term :=
  mul (const 2) (mul (mul (clkNumBlocksT τT) (const (3 * k + 1)))
      (mul (const (s + k + 4)) (clkBlockLenT τT)))

/-- The number of vertices `verticesN k s τ`. -/
def clkVerticesT (τT : Term) : Term :=
  add (mul (clkNumBlocksT τT) (const (3 * k + 2)))
    (mul (mul (clkNumBlocksT τT) (const (3 * k + 1))) (mul (const (s + k + 4)) (clkBlockLenT τT)))

/-- The local simulation radix `3^(4b) + |x| + s + 3`, with `nT` the input length. -/
def clkRadixT (nT τT : Term) : Term :=
  add (add (add (powT (const 3) (mul (const 4) (clkBlockLenT τT))) nT) (const s)) (const 3)

/-- The degree of a vertex. -/
def clkArityT (τT σT : Term) : Term → Term := arityNT k s (clkNumBlocksT τT) (clkBlockLenT τT) σT

/-- The ports of a vertex. -/
def clkPortT (τT σT : Term) : Term → Term → Term := portAtT k s (clkNumBlocksT τT) (clkBlockLenT τT)
    σT

/-- The weights of a vertex. -/
def clkWeightT (nT τT σT : Term) : Term → Term → Term :=
  weightNT k s e machine (clkRadixT s nT τT) nT (clkNumBlocksT τT) (clkBlockLenT τT) σT

/-- The row end of edge `iT`. -/
def edgeUT (τT σT iT : Term) : Term :=
  explicitSrcT k (clkNumBlocksT τT) (letterBitsT k s (clkBlockLenT τT)) σT iT

/-- The column end of edge `iT`. -/
def edgeWT (τT iT : Term) : Term :=
  explicitTgtT k (clkNumBlocksT τT) (letterBitsT k s (clkBlockLenT τT)) iT

/-- The table of vertex `vT` at the port bits `AT`, reduced mod `pT`. -/
def evalAtT (nT τT σT pT vT AT : Term) : Term := mod (clkWeightT k s machine e nT τT σT vT AT) pT

end Terms

section Denote

variable {machine e} {w : List Bool} {env : List ℕ} {nT τT σT : Term} {t σ : ℕ}

section Clock

variable (hτ : StableAt w τT env) (hτv : τT.denote w env = t)
include hτ hτv

theorem denote_clkBlockLenT : (clkBlockLenT τT).denote w env = blockLength t := by
  rw [clkBlockLenT, denote_clogT (hτ.add (stableAt_const _ _)) (by simp), denote_add, hτv,
      denote_const]
  rfl

theorem StableAt.clkBlockLenT : StableAt w (NetTerm.clkBlockLenT τT) env :=
  have _ := hτv
  StableAt.clogT (hτ.add (stableAt_const _ _)) (by simp)

theorem denote_clkNumBlocksT : (clkNumBlocksT τT).denote w env = numBlocks t := by
  rw [clkNumBlocksT, denote_ceilDivT, hτv, denote_clkBlockLenT hτ hτv, numBlocks,
      Nat.ceilDiv_eq_add_pred_div]

theorem StableAt.clkNumBlocksT : StableAt w (NetTerm.clkNumBlocksT τT) env := fun extra => by
  rw [denote_clkNumBlocksT (hτ.extend extra) (by rw [hτ extra, hτv]), denote_clkNumBlocksT hτ hτv]

theorem denote_clkEdgesT : (clkEdgesT k s τT).denote w env = edgesN k s t := by
  simp only [clkEdgesT, denote_mul, denote_const, denote_clkNumBlocksT hτ hτv, denote_clkBlockLenT
      hτ hτv,
    edgesN, Turing.MultiTapePTM.letterBits]

theorem StableAt.clkEdgesT : StableAt w (NetTerm.clkEdgesT k s τT) env := fun extra => by
  rw [denote_clkEdgesT (hτ.extend extra) (by rw [hτ extra, hτv]), denote_clkEdgesT hτ hτv]

theorem denote_clkVerticesT : (clkVerticesT k s τT).denote w env = verticesN k s t := by
  simp only [clkVerticesT, denote_add, denote_mul, denote_const, denote_clkNumBlocksT hτ hτv,
    denote_clkBlockLenT hτ hτv, verticesN, MultiTapePTM.letterBits]

theorem StableAt.clkVerticesT : StableAt w (NetTerm.clkVerticesT k s τT) env := fun extra => by
  rw [denote_clkVerticesT (hτ.extend extra) (by rw [hτ extra, hτv]), denote_clkVerticesT hτ hτv]

theorem stableAt_letterBitsT : StableAt w (letterBitsT k s (clkBlockLenT τT)) env :=
  (stableAt_const _ _).mul (StableAt.clkBlockLenT hτ hτv)

theorem denote_letterBitsT :
    (letterBitsT k s (clkBlockLenT τT)).denote w env = letterBits k s (blockLength t) := by
  simp [letterBitsT, letterBits, denote_clkBlockLenT hτ hτv]

/-- The number of edges. -/
theorem denote_clkEdgesT_M {p : ℕ} {x : List Bool} (hd : RowsFirst machine e x t σ) :
    (clkEdgesT k s τT).denote w env = (blockEdgeNet machine e p x t σ hd).M := by
  rw [denote_clkEdgesT hτ hτv, M_blockEdgeNet]

/-- The number of vertices. -/
theorem denote_clkVerticesT_length {x : List Bool} :
    (clkVerticesT k s τT).denote w env =
        (blockNetworkOf machine e (x, t, σ)).2.vertices.length := by
  rw [denote_clkVerticesT hτ hτv, length_vertices]

variable (hσ : StableAt w σT env) (hσv : σT.denote w env = σ)
include hσ hσv

omit hσv in
theorem StableAt.edgeUT {iT : Term} (hi : StableAt w iT env) : StableAt w
    (NetTerm.edgeUT k s τT σT iT) env :=
  StableAt.explicitSrcT k (StableAt.clkNumBlocksT hτ hτv) (stableAt_letterBitsT hτ hτv) hσ hi

/-- The row end of edge `i`. -/
theorem denote_edgeUT {p : ℕ} (hd : RowsFirst machine e w t σ) {iT : Term}
    (hi : StableAt w iT env) {i : ℕ} (hiv : iT.denote w env = i)
    (hiM : i < (blockEdgeNet machine e p w t σ hd).M) :
    (edgeUT k s τT σT iT).denote w env = ((blockEdgeNet machine e p w t σ hd).u ⟨i, hiM⟩ : ℕ) := by
  rw [val_u, NetTerm.edgeUT, denote_explicitSrcT k (StableAt.clkNumBlocksT hτ hτv)
    (stableAt_letterBitsT hτ hτv) hσ hi, denote_clkNumBlocksT hτ hτv, denote_letterBitsT hτ hτv,
        hσv, hiv]

omit hσ hσv in
theorem StableAt.edgeWT {iT : Term} (hi : StableAt w iT env) : StableAt w (NetTerm.edgeWT k s τT iT)
    env :=
  fun extra => by
    rw [NetTerm.edgeWT, denote_explicitTgtT, denote_explicitTgtT, (StableAt.clkNumBlocksT hτ hτv)
        extra,
      (stableAt_letterBitsT hτ hτv) extra, hi extra]

omit hσ hσv in
/-- The column end of edge `i`. -/
theorem denote_edgeWT {p : ℕ} (hd : RowsFirst machine e w t σ) {iT : Term}
    {i : ℕ} (hiv : iT.denote w env = i)
    (hiM : i < (blockEdgeNet machine e p w t σ hd).M) :
    (edgeWT k s τT iT).denote w env = ((blockEdgeNet machine e p w t σ hd).w ⟨i, hiM⟩ : ℕ) := by
  rw [val_w, NetTerm.edgeWT, denote_explicitTgtT, denote_clkNumBlocksT hτ hτv, denote_letterBitsT hτ
      hτv, hiv]

omit hσv in
theorem StableAt.clkArityT {vT : Term} (hv : StableAt w vT env) :
    StableAt w (NetTerm.clkArityT k s τT σT vT) env :=
  StableAt.arityNT (StableAt.clkNumBlocksT hτ hτv) (StableAt.clkBlockLenT hτ hτv) hσ hv

/-- The degree of vertex `v`. -/
theorem denote_clkArityT {p : ℕ} (hd : RowsFirst machine e w t σ) {vT : Term}
    (hvs : StableAt w vT env) {v : Fin (blockNetworkOf machine e (w, t, σ)).2.vertices.length}
    (hvv : vT.denote w env = v) :
    (clkArityT k s τT σT vT).denote w env =
        ((blockEdgeNet machine e p w t σ hd).ports v).length := by
  rw [length_ports, clkArityT, denote_arityNT (StableAt.clkNumBlocksT hτ hτv)
      (StableAt.clkBlockLenT hτ hτv)
    hσ hvs, denote_clkNumBlocksT hτ hτv, denote_clkBlockLenT hτ hτv, hσv, hvv]
  rfl

omit hσv in
theorem StableAt.clkPortT {vT jT : Term} (hv : StableAt w vT env) (hj : StableAt w jT env) :
    StableAt w (NetTerm.clkPortT k s τT σT vT jT) env := fun extra => by
  have hq := StableAt.clkNumBlocksT hτ hτv
  have hb := StableAt.clkBlockLenT hτ hτv
  rw [NetTerm.clkPortT, denote_portAtT (hq.extend extra) (hb.extend extra) (hσ.extend extra)
      (hv.extend extra) jT
    (hj.extend extra), denote_portAtT hq hb hσ hv jT hj, hq extra, hb extra, hσ extra, hv extra, hj
        extra]

/-- The `j`-th port of vertex `v`. -/
theorem denote_clkPortT {p : ℕ} (hd : RowsFirst machine e w t σ) {vT jT : Term}
    (hvs : StableAt w vT env) {v : Fin (blockNetworkOf machine e (w, t, σ)).2.vertices.length}
    (hvv : vT.denote w env = v) (hjs : StableAt w jT env)
    {j : Fin ((blockEdgeNet machine e p w t σ hd).ports v).length}
    (hjv : jT.denote w env = j) :
    (clkPortT k s τT σT vT jT).denote w env =
      (((blockEdgeNet machine e p w t σ hd).ports v).get j : ℕ) := by
  rw [val_get_ports, clkPortT, denote_portAtT (StableAt.clkNumBlocksT hτ hτv)
      (StableAt.clkBlockLenT hτ hτv)
    hσ hvs jT hjs, denote_clkNumBlocksT hτ hτv, denote_clkBlockLenT hτ hτv, hσv, hvv, hjv]
  rfl

end Clock

variable (hn : StableAt w nT env) (hnv : nT.denote w env = w.length)
  (hτ : StableAt w τT env) (hτv : τT.denote w env = t)
include hn hnv hτ hτv

omit hn in
theorem denote_clkRadixT : (clkRadixT s nT τT).denote w env = radix (blockLength t) w.length s := by
  simp only [clkRadixT, denote_add, denote_const, powT_denote _ _ _ (stableAt_const _ _),
    denote_mul, denote_clkBlockLenT hτ hτv, hnv, radix]

theorem StableAt.clkRadixT : StableAt w (NetTerm.clkRadixT s nT τT) env := fun extra => by
  rw [denote_clkRadixT (by rw [hn extra, hnv]) (hτ.extend extra) (by rw [hτ extra, hτv]),
    denote_clkRadixT hnv hτ hτv]

variable (hσ : StableAt w σT env) (hσv : σT.denote w env = σ)
include hσ hσv

omit hσv in
theorem StableAt.clkWeightT {vT AT : Term} (hv : StableAt w vT env) (hA : StableAt w AT env) :
    StableAt w (NetTerm.clkWeightT k s machine e nT τT σT vT AT) env := fun extra => by
  have hq := StableAt.clkNumBlocksT hτ hτv
  have hb := StableAt.clkBlockLenT hτ hτv
  have hR := StableAt.clkRadixT (s := s) hn hnv hτ hτv
  have hbpos : 0 < (NetTerm.clkBlockLenT τT).denote w env := by
    rw [denote_clkBlockLenT hτ hτv]; exact one_le_blockLength _
  have hRv := denote_clkRadixT (s := s) hnv hτ hτv
  rw [NetTerm.clkWeightT, denote_weightNT (hR.extend extra) (hn.extend extra) (hq.extend extra)
      (hb.extend extra)
      (hσ.extend extra) (hv.extend extra) (hA.extend extra) (by rw [hb extra]; exact hbpos)
      (by rw [hR extra, hb extra, hRv, denote_clkBlockLenT hτ hτv])
      (by rw [hn extra, hnv]),
    denote_weightNT hR hn hq hb hσ hv hA hbpos (by rw [hRv, denote_clkBlockLenT hτ hτv]) hnv,
    hq extra, hb extra, hσ extra, hv extra, hA extra]

omit hσv in
theorem StableAt.evalAtT {pT vT AT : Term} (hp : StableAt w pT env) (hv : StableAt w vT env)
    (hA : StableAt w AT env) : StableAt w (NetTerm.evalAtT k s machine e nT τT σT pT vT AT) env :=
  (StableAt.clkWeightT hn hnv hτ hτv hσ hv hA).mod hp

/-- The table of vertex `v` at the bits of `A` on its ports (bit `j` on the `j`-th port), mod
`p`. -/
theorem denote_evalAtT {p : ℕ} (hd : RowsFirst machine e w t σ) {pT vT AT : Term}
    (hpv : pT.denote w env = p) (hvs : StableAt w vT env)
    {v : Fin (blockNetworkOf machine e (w, t, σ)).2.vertices.length}
    (hvv : vT.denote w env = v) (hAs : StableAt w AT env) {A : ℕ} (hAv : AT.denote w env = A) :
    (evalAtT k s machine e nT τT σT pT vT AT).denote w env =
      ((blockEdgeNet machine e p w t σ hd).eval v
        (List.ofFn fun j : Fin ((blockEdgeNet machine e p w t σ hd).ports v).length =>
          A.testBit j)).val := by
  have hq := StableAt.clkNumBlocksT hτ hτv
  have hb := StableAt.clkBlockLenT hτ hτv
  have hR := StableAt.clkRadixT (s := s) hn hnv hτ hτv
  have hbpos : 0 < (clkBlockLenT τT).denote w env := by
    rw [denote_clkBlockLenT hτ hτv]; exact one_le_blockLength _
  rw [val_eval_ofFn, NetTerm.evalAtT, denote_mod, clkWeightT,
    denote_weightNT hR hn hq hb hσ hvs hAs hbpos
      (by rw [denote_clkRadixT hnv hτ hτv, denote_clkBlockLenT hτ hτv]) hnv,
    denote_clkNumBlocksT hτ hτv, denote_clkBlockLenT hτ hτv, hσv, hvv, hAv, hpv]
  rfl

/-- The table of vertex `v` at bits `bs` on its ports, as the number `lsbValue bs`, mod `p`. -/
theorem denote_evalAtT_bits {p : ℕ} (hd : RowsFirst machine e w t σ) {pT vT AT : Term}
    (hpv : pT.denote w env = p) (hvs : StableAt w vT env)
    {v : Fin (blockNetworkOf machine e (w, t, σ)).2.vertices.length}
    (hvv : vT.denote w env = v) (hAs : StableAt w AT env) {bs : List Bool}
    (hbs : bs.length = ((blockEdgeNet machine e p w t σ hd).ports v).length)
    (hAv : AT.denote w env = Cslib.BitString.lsbValue bs) :
    (evalAtT k s machine e nT τT σT pT vT AT).denote w env =
      ((blockEdgeNet machine e p w t σ hd).eval v bs).val := by
  have hlt := Cslib.BitString.lsbValue_lt bs
  rw [hbs, length_ports] at hlt
  rw [denote_evalAtT hn hnv hτ hτv hσ hσv hd hpv hvs hvv hAs hAv, val_eval_ofFn, val_eval hd v bs
      hbs,
    Nat.mod_eq_of_lt hlt]

end Denote

/-! ### Tiers -/

section Tiers

variable {machine e} {w : List Bool} {L : ℕ} {env : List ℕ} {nT τT : Term} {t : ℕ}

theorem t_le_edgesN (k s t : ℕ) : t ≤ edgesN k s t :=
  (le_paddedTime t).trans (ProgTerm.paddedTime_le_edgesN k s t)

theorem verticesN_le_edgesN : verticesN k s t ≤ edgesN k s t := by
  simp only [verticesN, edgesN, Turing.MultiTapePTM.letterBits]
  have hb : 1 ≤ blockLength t := Cslib.Complexity.CountingSimulation.one_le_blockLength _
  set P := (3 * k + 1) * ((s + k + 4) * blockLength t)
  have hlb : 4 ≤ (s + k + 4) * blockLength t :=
    le_trans (by omega : 4 ≤ s + k + 4) (Nat.le_mul_of_pos_right _ hb)
  have h1 : 3 * k + 2 ≤ P := le_trans (by omega : 3 * k + 2 ≤ (3 * k + 1) * 4)
      (Nat.mul_le_mul_left _ hlb)
  have h2 : numBlocks t * (3 * k + 2) ≤ numBlocks t * P := Nat.mul_le_mul_left _ h1
  have e : numBlocks t * (3 * k + 1) * ((s + k + 4) * blockLength t) = numBlocks t * P := by
    simp only [P]; ring
  rw [e]
  omega

theorem edgesN_lt {t : ℕ} (hcube : edgesN k s t ^ 3 < 2 ^ L) : edgesN k s t < 2 ^ L :=
  lt_of_le_of_lt (Nat.le_self_pow (by norm_num) _) hcube

section Clock

variable (hL : 8 ≤ L) (hτ : Tm w L 1 τT env) (hτs : StableAt w τT env) (hτv : τT.denote w env = t)
  (ht : 2 ≤ t) (hcube : edgesN k s t ^ 3 < 2 ^ L) (hconst : 4 * k + s + 100 < 2 ^ L)
include hL hτ hτs hτv ht hcube hconst


theorem t_lt_two_pow : t < 2 ^ L := lt_of_le_of_lt (t_le_edgesN k s t) (edgesN_lt hcube)

theorem tm_clkBlockLenT : Tm w L 1 (clkBlockLenT τT) env := by
  have htL := t_lt_two_pow hL hτ hτs hτv ht hcube hconst
  refine tm_retier (d := 100) ?_ (StableAt.clkBlockLenT hτs hτv) ?_
  · have c1 : (1 : ℕ) < 2 ^ L := lit_lt_two_pow (by norm_num) (by omega)
    have c2 : (2 : ℕ) < 2 ^ L := lit_lt_two_pow (by norm_num) (by omega)
    have c0 : (0 : ℕ) < 2 ^ L := by positivity
    unfold clkBlockLenT clogT
    tame
  · rw [denote_clkBlockLenT hτs hτv, one_mul]
    exact lt_of_le_of_lt (blockLength_le_self t ht) htL

theorem tm_clkNumBlocksT : Tm w L 1 (clkNumBlocksT τT) env := by
  have htL := t_lt_two_pow hL hτ hτs hτv ht hcube hconst
  have hb := tm_clkBlockLenT hL hτ hτs hτv ht hcube hconst
  refine tm_retier (d := 100) ?_ (StableAt.clkNumBlocksT hτs hτv) ?_
  · have c1 : (1 : ℕ) < 2 ^ L := lit_lt_two_pow (by norm_num) (by omega)
    unfold clkNumBlocksT ceilDivT
    tame
  · rw [denote_clkNumBlocksT hτs hτv, one_mul]
    have hb1 : 1 ≤ blockLength t := Cslib.Complexity.CountingSimulation.one_le_blockLength _
    have h1 : numBlocks t ≤ t := by
      unfold numBlocks
      rw [Nat.ceilDiv_eq_add_pred_div, Nat.div_le_iff_le_mul_add_pred (by omega)]
      have : t ≤ blockLength t * t := Nat.le_mul_of_pos_left _ hb1
      omega
    omega

theorem tm_clkEdgesT : Tm w L 1 (clkEdgesT k s τT) env := by
  have hb := tm_clkBlockLenT hL hτ hτs hτv ht hcube hconst
  have hq := tm_clkNumBlocksT hL hτ hτs hτv ht hcube hconst
  refine tm_retier (d := 16) ?_ (StableAt.clkEdgesT hτs hτv) ?_
  · have c1 : 3 * k + 1 < 2 ^ L := by omega
    have c2 : s + k + 4 < 2 ^ L := by omega
    have c3 : (2 : ℕ) < 2 ^ L := lit_lt_two_pow (by norm_num) (by omega)
    unfold clkEdgesT
    tame
  · rw [denote_clkEdgesT hτs hτv, one_mul]; exact edgesN_lt hcube

theorem tm_clkVerticesT : Tm w L 1 (clkVerticesT k s τT) env := by
  have hb := tm_clkBlockLenT hL hτ hτs hτv ht hcube hconst
  have hq := tm_clkNumBlocksT hL hτ hτs hτv ht hcube hconst
  refine tm_retier (d := 100) ?_ (StableAt.clkVerticesT hτs hτv) ?_
  · have c1 : 3 * k + 2 < 2 ^ L := by omega
    have c2 : s + k + 4 < 2 ^ L := by omega
    unfold clkVerticesT
    tame
  · rw [denote_clkVerticesT hτs hτv, one_mul]
    exact lt_of_le_of_lt (verticesN_le_edgesN (k := k) (s := s) (t := t))
      (edgesN_lt hcube)

theorem tm_clkRadixT (hn : Tm w L 1 nT env) (hns : StableAt w nT env)
    (hnv : nT.denote w env = w.length)
    (hRl : LocalSim.radix (blockLength t) w.length s < 2 ^ L) :
    Tm w L 1 (clkRadixT s nT τT) env := by
  have hb := tm_clkBlockLenT hL hτ hτs hτv ht hcube hconst
  have hbs := StableAt.clkBlockLenT hτs hτv
  have hpow : Tm w L 1 (powT (const 3) (mul (const 4) (clkBlockLenT τT))) env := by
    refine t_powT (t_const (lit_lt_two_pow (by omega) (by omega))) (stableAt_const _ _)
      (t_mul (t_const (lit_lt_two_pow_big (by omega) (by omega))) hb (by omega)) (by omega) le_rfl
      (by omega) (fun pre _ => ?_) (by omega) (by omega)
    rw [denote_const, denote_mul, denote_const, hbs pre, denote_clkBlockLenT hτs hτv, one_mul]
    unfold LocalSim.radix at hRl
    omega
  refine tm_retier (d := 100) ?_ (StableAt.clkRadixT hns hnv hτs hτv) ?_
  · have c1 : s < 2 ^ L := by omega
    have c2 : (3 : ℕ) < 2 ^ L := lit_lt_two_pow (by norm_num) (by omega)
    unfold clkRadixT; tame
  · rw [denote_clkRadixT hnv hτs hτv, one_mul]; exact hRl

end Clock

set_option maxHeartbeats 1000000 in
-- Instantiating the accessor lemmas involves many large terms, as in `tm_accessors`.
/-- **Tiers of the network accessors** at the clock `τT` and the input length `nT` (the
clock-generic form of `tm_accessors`). -/
theorem tm_clkAccessors {σT : Term} {D0 : ℕ}
    (hL : 8 ≤ L) (hN : Tm w L 1 nT env) (hNs : StableAt w nT env) (hNv : nT.denote w env = w.length)
    (hτ : Tm w L 1 τT env) (hτs : StableAt w τT env) (hτv : τT.denote w env = t)
    (ht : 2 ≤ t) (hcube : edgesN k s t ^ 3 < 2 ^ L) (hconst : 4 * k + s + 100 < 2 ^ L)
    (hkey : keyCount k s * k + keyCount k s + width k + 3 ^ k < 2 ^ L)
    (hRw : LocalSim.radix (blockLength t) w.length s ^ width k < 2 ^ L)
    (h3b : 3 ^ (3 * blockLength t) < 2 ^ L)
    (hccv : (s + 1) * (blockLength t ^ (k + 1) * 3) < 2 ^ L)
    (hm0 : MultiTapePTM.letterBits k s (blockLength t) < L)
    (hσ : Tm w L 1 σT env) (hσs : StableAt w σT env)
    (hD0 : D0 < L)
    (hdeg : ∀ v < verticesN k s t,
      (MultiTapePTM.explicitPortsNum k (numBlocks t) (MultiTapePTM.letterBits k s (blockLength t))
        (σT.denote w env) v).length ≤ D0) :
    TmF w L (clkArityT k s τT σT) 4 1 env ∧
      TmF2 w L (clkPortT k s τT σT) 4 4 1 env ∧
      TmF2v w L (clkWeightT k s machine e nT τT σT) 4 (verticesN k s t) 4 1 env ∧
      TmFv w L (fun e' => pow2 (clkArityT k s τT σT e')) 4 (verticesN k s t) 1 env := by
  set n := w.length with hn_def
  set b := blockLength t with hb_def
  have hL2 : 2 ≤ L := by omega
  have hp3k : 0 < 3 ^ k := by positivity
  have hp4b : 0 < 3 ^ (4 * b) := by positivity
  have hp3b : 0 < 3 ^ (3 * b) := by positivity
  have hpbk : 0 ≤ b ^ (k + 1) := Nat.zero_le _
  have hconst' : 4 * k + s + 100 < 2 ^ L := hconst
  have hq := tm_clkNumBlocksT hL hτ hτs hτv ht hcube hconst
  have hb := tm_clkBlockLenT hL hτ hτs hτv ht hcube hconst
  have hqs := StableAt.clkNumBlocksT hτs hτv
  have hqv := denote_clkNumBlocksT hτs hτv
  have hbs := StableAt.clkBlockLenT hτs hτv
  have hbv : (clkBlockLenT τT).denote w env = b := denote_clkBlockLenT hτs hτv
  have hbpos : 0 < b := Cslib.Complexity.CountingSimulation.one_le_blockLength _
  have hbp : Pos w L (clkBlockLenT τT) env := Pos.of_stable hbs (by rw [hbv]; exact hbpos)
  have hbm : b ≤ MultiTapePTM.letterBits k s b := by
    unfold MultiTapePTM.letterBits; nlinarith
  have hbL : b < L := by omega
  have hRle : LocalSim.radix b n s ≤ LocalSim.radix b n s ^ width k := by
    have : 0 < LocalSim.radix b n s := by unfold LocalSim.radix; positivity
    exact Nat.le_self_pow (by unfold width; omega) _
  have hR := tm_clkRadixT (s := s) hL hτ hτs hτv ht hcube hconst hN hNs hNv
      (lt_of_le_of_lt hRle hRw)
  have hRs := StableAt.clkRadixT (s := s) hNs hNv hτs hτv
  have hRv := denote_clkRadixT (s := s) hNv hτs hτv
  have hRpos : Pos w L (clkRadixT s nT τT) env :=
    Pos.of_stable hRs (by rw [hRv]; unfold LocalSim.radix; positivity)
  have hinit : LocalSim.stc e (some machine.initial) < 2 ^ L := lt_of_lt_of_le (stc_lt e _)
      (by omega)
  have hwk : width k < 2 ^ L := by omega
  have hW : Le w L (const (width k)) (width k) env := Le.of_stable (stableAt_const _ _) le_rfl
  have hpowR : TmFv w L (fun i => powT (clkRadixT s nT τT) i) 4 (width k) 1 env :=
    fun env' he' i hi his
        hiv => t_powT_lt (hR.ext he') (hRs.extend' he') hi (by omega) hiv (by omega)
      le_rfl (by rw [hRs.extend'_eq he', hRv, one_mul]; exact hRw) (by omega) (by omega)
  have h3 : TmFv w L (fun j => powT (const 3) j) 8 (3 * b) 1 env :=
    fun env' he' j hj hjs
        hjv => t_powT_lt (t_const (by omega)) (stableAt_const _ _) hj (by omega) hjv
      (by omega) le_rfl (by rw [denote_const, one_mul]; exact h3b) (by omega) (by omega)
  have h3bLe : Le w L (mul (const 3) (clkBlockLenT τT)) (3 * b) env :=
    Le.of_stable ((stableAt_const _ _).mul hbs) (by rw [denote_mul, denote_const, hbv])
  have hbk : b ^ (k + 1) < 2 ^ L := by
    have h1 : b ^ (k + 1) ≤ b ^ (k + 1) * 3 := Nat.le_mul_of_pos_right _ (by norm_num)
    have h2 := Nat.le_mul_of_pos_left (b ^ (k + 1) * 3) (by omega : 0 < s + 1)
    omega
  have hcr : Tm w L 1 (powT (clkBlockLenT τT) (const (k + 1))) env :=
    tm_powT_stable hL hb hbs (t_const (by omega)) (stableAt_const _ _) (by omega) (by omega)
      (by rw [hbv, denote_const]; exact hbk)
  have hcc : Tm w L 1 (ccountT k s (clkBlockLenT τT)) env := by
    refine tm_retier (d := 3) (by unfold ccountT cradT; tame) ((stableAt_const _ _).mul
      ((hbs.powT (stableAt_const _ _)).mul (stableAt_const _ _))) ?_
    simp only [ccountT, cradT, denote_mul, denote_const, powT_denote _ _ _ hbs, hbv, one_mul]
    exact hccv
  have h2b : Tm w L 1 (pow2 (clkBlockLenT τT)) env :=
    t_pow2_stable hb (by omega) hbs (by rw [hbv, one_mul]; exact hbL) (by omega) hL2
  have hfSt : TmF w L (tabT (fSt e machine) (keyCount k s)) 16 1 env :=
    tm_tabT _ _ hL (by omega)
        (fun i _ => by have := (tables_le (e := e) (machine := machine) i).1; omega)
  have hfIn : TmF w L (tabT (fIn e machine) (keyCount k s)) 16 1 env :=
    tm_tabT _ _ hL (by omega)
        (fun i _ => by have := (tables_le (e := e) (machine := machine) i).2.1; omega)
  have hfOut : TmF w L (tabT (fOut e machine) (keyCount k s)) 16 1 env :=
    tm_tabT _ _ hL (by omega) (fun i _ => by
      have := (tables_le (e := e) (machine := machine) i).2.2.1; omega)
  have hfEmit : TmF w L (tabT fEmit 9) 16 1 env :=
    tm_tabT _ _ hL (by omega) (fun i _ => by
      have := (tables_le (e := e) (machine := machine) i).2.2.2.1; omega)
  have hfW : TmF w L (tabT (fW e machine) (keyCount k s * k)) 16 1 env :=
    tm_tabT _ _ hL (by omega) (fun i _ => by
      have := (tables_le (e := e) (machine := machine) i).2.2.2.2.1; omega)
  have hfM : TmF w L (tabT (fM e machine) (keyCount k s * k)) 16 1 env :=
    tm_tabT _ _ hL (by omega) (fun i _ => by
      have := (tables_le (e := e) (machine := machine) i).2.2.2.2.2; omega)
  have hK : Le w L (const k) k env := Le.of_stable (stableAt_const _ _) le_rfl
  have hpow3 : TmFv w L (fun h => powT (const 3) h) 4 k 1 env :=
    fun env' he' j hj hjs
        hjv => t_powT_lt (t_const (by omega)) (stableAt_const _ _) hj (by omega) hjv
      (by omega) le_rfl (by rw [denote_const, one_mul]; omega) (by omega) (by omega)
  have hrun := tm_runT (e := e) (machine := machine) (bT := clkBlockLenT τT) hL hR hRpos hN hb
    hconst' hwk (by omega) (by omega) hW hpowR hK hpow3 hfSt hfIn hfOut hfEmit hfW hfM
  have hlet := tm_pow2_letter (w := w) (env := env) hm0 hL
  have hletLe : Le w L (letterBitsT k s (clkBlockLenT τT)) (MultiTapePTM.letterBits k s b) env :=
    Le.of_stable ((stableAt_const _ _).mul hbs) (by
      rw [letterBitsT, denote_mul, denote_const, hbv]; unfold MultiTapePTM.letterBits; exact le_rfl)
  have hm0' : MultiTapePTM.letterBits k s b < 2 ^ L := lt_trans hm0 Nat.lt_two_pow_self
  have hm1 := tm_letterBitsT hL hR hRpos hN hq hb hbs hbv hbpos hbp hσ hconst' hinit hwk hW hpowR
    h3 h3bLe hcr hcc h2b hrun hlet hletLe hm0'
  have hpa := tm_pow2_arityNT (mv := verticesN k s t) hL hq hb hσ hqs hbs hσs
    (by rw [hqv, hbv]; exact hdeg) hD0 hconst'
  have hwt := tm_weightNT1 hL hR hRpos hN hq hb hbs hbv hbpos hbp hσ hconst' hinit hwk hW hpowR
    h3 h3bLe hcr hcc h2b hrun hlet hletLe hm0' hpa (Nat.pow_lt_pow_right (by norm_num) hbL)
  have hEs : StableAt w (edgesT k s (clkNumBlocksT τT) (clkBlockLenT τT)) env := fun extra => by
    rw [denote_edgesT, denote_edgesT, hqs extra, hbs extra]
  have hEv : (edgesT k s (clkNumBlocksT τT) (clkBlockLenT τT)).denote w env = edgesN k s t := by
    rw [denote_edgesT, hqv, hbv]
  have hE : (edgesT k s (clkNumBlocksT τT) (clkBlockLenT τT)).denote w env *
      (edgesT k s (clkNumBlocksT τT) (clkBlockLenT τT)).denote w env < 2 ^ L := by
    rw [hEv]
    have h1 : 1 ≤ edgesN k s t := le_trans (by omega) (t_le_edgesN k s t)
    have : edgesN k s t * edgesN k s t ≤ edgesN k s t ^ 3 := by
      rw [show edgesN k s t ^ 3 = edgesN k s t * edgesN k s t * edgesN k s t by ring]
      exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hcst : 4 * k + 100 < 2 ^ L := by omega
  exact ⟨tm_arityNT1 hL hq hb hσ hm1 hcst hEs hE, tm_portAtT1 hL hq hb hσ hm1 hcst hEs hE, hwt, hpa⟩

set_option maxHeartbeats 1000000 in
-- Instantiating the accessor lemmas involves many large terms, as in `tm_accessors`.
/-- **Tiers of the network terms** at the clock `τT` and the input length `nT`, for a stable
schedule term of tier `1` and a prime term of any tier: the numbers of edges and vertices, the
degree, the ports and the tables mod `p` have tier `1`, the ends tier `24`. -/
theorem tm_netTerms {σT pT : Term} {D0 dp : ℕ}
    (hL : 8 ≤ L) (hN : Tm w L 1 nT env) (hNs : StableAt w nT env) (hNv : nT.denote w env = w.length)
    (hτ : Tm w L 1 τT env) (hτs : StableAt w τT env) (hτv : τT.denote w env = t)
    (ht : 2 ≤ t) (hcube : edgesN k s t ^ 3 < 2 ^ L) (hconst : 4 * k + s + 100 < 2 ^ L)
    (hkey : keyCount k s * k + keyCount k s + width k + 3 ^ k < 2 ^ L)
    (hRw : LocalSim.radix (blockLength t) w.length s ^ width k < 2 ^ L)
    (h3b : 3 ^ (3 * blockLength t) < 2 ^ L)
    (hccv : (s + 1) * (blockLength t ^ (k + 1) * 3) < 2 ^ L)
    (hm0 : letterBits k s (blockLength t) < L)
    (hσ : Tm w L 1 σT env) (hσs : StableAt w σT env)
    (hD0 : D0 < L)
    (hdeg : ∀ v < verticesN k s t,
      (explicitPortsNum k (numBlocks t) (letterBits k s (blockLength t)) (σT.denote w env) v).length
          ≤ D0)
    (hp : Tm w L dp pT env) :
    Tm w L 1 (clkEdgesT k s τT) env ∧ Tm w L 1 (clkVerticesT k s τT) env ∧
      TmF w L (edgeUT k s τT σT) 16 24 env ∧ TmF w L (edgeWT k s τT) 16 24 env ∧
      TmF w L (clkArityT k s τT σT) 4 1 env ∧
      TmF2 w L (clkPortT k s τT σT) 4 4 1 env ∧
      TmF2v w L (evalAtT k s machine e nT τT σT pT) 4 (verticesN k s t) 4 1 env ∧
      TmFv w L (fun v => pow2 (clkArityT k s τT σT v)) 4 (verticesN k s t) 1 env := by
  obtain ⟨har, hpo, hwt, hpa⟩ := tm_clkAccessors (e := e) (machine := machine) hL hN hNs hNv hτ hτs
      hτv ht
    hcube hconst hkey hRw h3b hccv hm0 hσ hσs hD0 hdeg
  have hq := tm_clkNumBlocksT hL hτ hτs hτv ht hcube hconst
  have hbs := StableAt.clkBlockLenT hτs hτv
  have hm : Tm w L 1 (letterBitsT k s (clkBlockLenT τT)) env := by
    have hb := tm_clkBlockLenT hL hτ hτs hτv ht hcube hconst
    have c1 : s + k + 4 < 2 ^ L := by omega
    refine tm_retier (d := 4) (by unfold letterBitsT; tame) ((stableAt_const _ _).mul hbs) ?_
    rw [denote_letterBitsT hτs hτv, one_mul]
    exact lt_trans hm0 Nat.lt_two_pow_self
  have hcst : 4 * k + 100 < 2 ^ L := by omega
  refine ⟨tm_clkEdgesT hL hτ hτs hτv ht hcube hconst,
    tm_clkVerticesT hL hτ hτs hτv ht hcube hconst,
    tm_explicitSrcT (k := k) hL hq hm hσ hcst, tm_explicitTgtT (k := k) hL hq hm hσ hcst, har, hpo,
    fun env' he' v A hv hvs hvv hA
        hAs => t_mod_left (hwt env' he' v A hv hvs hvv hA hAs) (hp.ext he'),
    hpa⟩

/-- **Tier `1` for the ends** of the edges `i < N`, for a schedule with a rows-first network. -/
theorem tm_ends1 {σT : Term} {σ : ℕ}
    (hL : 8 ≤ L) (hτ : Tm w L 1 τT env) (hτs : StableAt w τT env) (hτv : τT.denote w env = t)
    (ht : 2 ≤ t) (hcube : edgesN k s t ^ 3 < 2 ^ L) (hconst : 4 * k + s + 100 < 2 ^ L)
    (hm0 : letterBits k s (blockLength t) < L)
    (hσ : Tm w L 1 σT env) (hσs : StableAt w σT env) (hσv : σT.denote w env = σ)
    (hd : RowsFirst machine e w t σ) :
    TmFv w L (edgeUT k s τT σT) 16 (edgesN k s t) 1 env ∧
      TmFv w L (edgeWT k s τT) 16 (edgesN k s t) 1 env := by
  have hq := tm_clkNumBlocksT hL hτ hτs hτv ht hcube hconst
  have hbs := StableAt.clkBlockLenT hτs hτv
  have hm : Tm w L 1 (letterBitsT k s (clkBlockLenT τT)) env := by
    have hb := tm_clkBlockLenT hL hτ hτs hτv ht hcube hconst
    have c1 : s + k + 4 < 2 ^ L := by omega
    refine tm_retier (d := 4) (by unfold letterBitsT; tame) ((stableAt_const _ _).mul hbs) ?_
    rw [denote_letterBitsT hτs hτv, one_mul]
    exact lt_trans hm0 Nat.lt_two_pow_self
  have hcst : 4 * k + 100 < 2 ^ L := by omega
  have hV : verticesN k s t < 2 ^ L :=
    lt_of_le_of_lt (verticesN_le_edgesN (k := k) (s := s) (t := t))
      (edgesN_lt hcube)
  -- the value of an edge argument
  have harg : ∀ env', Ext L env' env → ∀ i : Term, StableAt w i env' → Sm w L i (edgesN k s t) env'
      →
      i.denote w env' < (blockEdgeNet machine e 0 w t σ hd).M := fun env' he' i _ hiv => by
    have := hiv [] Small.nil
    rw [M_blockEdgeNet]
    simpa using this
  refine ⟨fun env' he' i hi his hiv => ?_, fun env' he' i hi his hiv => ?_⟩
  · have hτs' := hτs.extend' he'
    have hτv' : τT.denote w env' = t := by rw [hτs.extend'_eq he', hτv]
    refine tm_retier ((tm_explicitSrcT (k := k) hL hq hm hσ hcst).app he' hi)
      (StableAt.edgeUT hτs' hτv' (hσs.extend' he') his) ?_
    have hlt := harg env' he' i his hiv
    rw [denote_edgeUT hτs' hτv' (hσs.extend' he') (by rw [hσs.extend'_eq he', hσv]) hd his rfl hlt,
        one_mul]
    have h1 := ((blockEdgeNet machine e 0 w t σ hd).u ⟨_, hlt⟩).2
    have h2 : (blockNetworkOf machine e (w, t, σ)).2.vertices.length < 2 ^ L := by
      rw [length_vertices]; exact hV
    omega
  · have hτs' := hτs.extend' he'
    have hτv' : τT.denote w env' = t := by rw [hτs.extend'_eq he', hτv]
    refine tm_retier ((tm_explicitTgtT (k := k) hL hq hm hσ hcst).app he' hi)
      (StableAt.edgeWT hτs' hτv' his) ?_
    have hlt := harg env' he' i his hiv
    rw [denote_edgeWT hτs' hτv' (σ := σ) hd rfl hlt, one_mul]
    have h1 := ((blockEdgeNet machine e 0 w t σ hd).w ⟨_, hlt⟩).2
    have h2 : (blockNetworkOf machine e (w, t, σ)).2.vertices.length < 2 ^ L := by
      rw [length_vertices]; exact hV
    omega

end Tiers


/-! ### Axiom audit -/

end Cslib.Complexity.NtimeDspace.Cross.NetTerm
