/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler
public import CslibFrontier.Computability.Circuit.Frontier.Ledger.Basic
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Sweeping a program with a ledger

Let the special gates of a program `p` have a ledger in `M`, and let `p` accept the inputs whose
value at a wire `o` lies in a set `Acc`. Erase the special gates. A wire is *live*
(`Frontier.Live`) if it is an input or an ordinary gate of positive arity; the others are
constants of the erased program, among them the constants replacing the special gates. The
*live circuit* (`Frontier.liveCircuit`) is the erased program with every live wire as an output.
For a guess `m ∈ M`, the constraint network of the live circuit accepting every value
(`Frontier.Ledger.network`) is satisfied exactly by the run with guess `m`. Its graph and its
sites do not depend on `m`: they make up the *live network* (`Frontier.liveNetwork`), which has no
constraints and serves for the frontiers, components and inputs read of every guess.

**The ledger sweep** (`Frontier.Ledger.sweep`) is the sweep along a layout of the live network
(`Frontier.Network.frontierSweep`) whose extra message has two parts: the readout `L.readout m` of
the consistent guess `m = L.total (p.trace I x)` on the special gates, and the product of the
contributions of the wires whose vertices come first (the *ledger so far*). Two inputs with the
same message can be spliced (`Frontier.Ledger.mem_of_splice`): matching readouts give the exact
same erased constraint network; the two parts of the ledger multiply back to the second input's
consistent guess; and a consistent guess yields the true run.

**Tightened transitions (`|U|^k · |M|`, bounded also by `|M|^2`).** Because the readout stays
constant across step `t → t + 1` and the contribution of a newly processed signal vertex `w` is
determined by its outgoing head edge in `frontier π t ∪ frontier π (t + 1)` (or `touching W`), the
extra message `L.extra π (t + 1) x` is already determined by `L.extra π t x` and the edge values of
the step (`Frontier.Ledger.extra_succ_eq`). Thus each step multiplies the transition count only by
`min (|U| ^ k) |M| * |M|`, where `k = |{g // special g}|` (`Frontier.Ledger.ncard_extra_le`),
replacing the naive `|M| ^ 3` bound (`Frontier.Ledger.exists_ncard_le`).

## Main definitions

* `Cslib.Circuits.Frontier.Live`: the live wires of a program with erased special gates.
* `Cslib.Circuits.Frontier.liveCircuit`: the erased program with every live wire as an output.
* `Cslib.Circuits.Frontier.liveNetwork`, `Cslib.Circuits.Frontier.wiresIn`: its graph and
  sites, as a network without constraints, and the wires whose vertices lie in a set.
* `Cslib.Circuits.Frontier.Ledger.network`: its constraint network on a guess.
* `Cslib.Circuits.Frontier.Ledger.extra`, `Cslib.Circuits.Frontier.Ledger.sweep`: the extra
  message and sweep of a program with a ledger.

## Main results

* `Cslib.Circuits.Frontier.reach_input`, `Cslib.Circuits.Frontier.read_liveNetwork`: every input is
  a signal of `liveCircuit`, and `liveNetwork` reads every input.
* `Cslib.Circuits.Frontier.Ledger.trace_of_splice`, `Cslib.Circuits.Frontier.Ledger.mem_of_splice`:
  splicing two inputs whose readouts, partial ledgers and cut values agree.
* `Cslib.Circuits.Frontier.Ledger.run_eq_of_eqOn_readIn`: locality inside a closed set.
* `Cslib.Circuits.Frontier.Ledger.ncard_extra_le`: the extra message at time `t` takes at most
  `min (|U| ^ k) |M| * |M|` values.
* `Cslib.Circuits.Frontier.Ledger.ncard_transition_le_width`,
  `Cslib.Circuits.Frontier.Ledger.ncard_transition_le_readIn`: transitions by width and by the
  inputs read in a closed set.
* `Cslib.Circuits.Frontier.Ledger.exists_ncard_le`: counting along a layout of the components.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

universe v

variable {σ : Signature.{v}} {n s : ℕ} {U : Type*}

/-! ### The live circuit -/

variable (p : Program σ n s) (special : Fin s → Prop)

/-- A wire is *live*, once the special gates of `p` are erased, when it is an input or an
ordinary gate of positive arity. The other wires are constants of the erased program: the
constants replacing the special gates and the gates of arity zero. -/
def Live : Wire n s → Prop
  | .input _ => True
  | .gate g => ¬special g ∧ σ.Arity (p.lines g).op ≠ 0

variable [DecidablePred special]

/-- The *live circuit*: the program `p` with its special gates erased, and with every live wire
as an output. -/
noncomputable def liveCircuit :
    Circuit (σ.withConstants {g // special g}) n (Nat.card {w // Live p special w}) where
  program := p.eraseGates special
  outputs i := ((Finite.equivFin {w // Live p special w}).symm i).1

/-- The *live network*: the graph of the live circuit and the sites of its inputs, without
constraints. It does not depend on a ledger or a guess; its frontiers, components and inputs read
are those of the network of the live circuit on every guess (`Frontier.Ledger.network`). -/
noncomputable def liveNetwork (U : Type*) :
    Network U (Fin n) (Compiler.Vertex (liveCircuit p special))
      (Compiler.Edge (liveCircuit p special)) where
  toMultigraph := Compiler.graph (liveCircuit p special)
  site := Compiler.site (liveCircuit p special)
  Constraint _ _ _ := True
  constraint_congr _ _ _ _ _ _ _ h := h

variable {p special}

/-- The live wires are signals of the live circuit. -/
private theorem reach_of_live {w : Wire n s} (hw : Live p special w) :
    Compiler.Reach (liveCircuit p special) w := by
  have h := Compiler.Reach.output (c := liveCircuit p special)
    (Finite.equivFin {w // Live p special w} ⟨w, hw⟩)
  simpa [liveCircuit] using h

/-- The inputs are signals of the live circuit. -/
theorem reach_input (i : Fin n) : Compiler.Reach (liveCircuit p special) (.input i) :=
  reach_of_live trivial

/-- The inner gates of the live circuit are the ordinary inner gates. -/
theorem innerSize_liveCircuit :
    (liveCircuit p special).innerSize = (p.innerGates.filter fun g => ¬special g).card := by
  rw [Circuit.innerSize, ← Program.innerGates_eraseGates]
  rfl

/-- There are at most `n + s'` live wires, where `s'` counts the ordinary inner gates. -/
theorem card_live_le :
    Nat.card {w // Live p special w} ≤ n + (liveCircuit p special).innerSize := by
  rw [innerSize_liveCircuit, ← Nat.card_eq_finsetCard]
  calc Nat.card {w // Live p special w}
      ≤ Nat.card (Fin n ⊕ ↥(p.innerGates.filter fun g => ¬special g)) := by
        refine Nat.card_le_card_of_injective (fun w => match w with
          | ⟨.input i, _⟩ => .inl i
          | ⟨.gate g, h⟩ => .inr ⟨g, Finset.mem_filter.2 ⟨Program.mem_innerGates.2 h.2, h.1⟩⟩) ?_
        rintro ⟨w | w, hw⟩ ⟨w' | w', hw'⟩ h <;> simp_all
    _ = n + Nat.card ↥(p.innerGates.filter fun g => ¬special g) := by
        rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]

/-- The live network reads every input. -/
theorem read_liveNetwork : (liveNetwork p special U).read = univ :=
  eq_univ_of_forall fun i => ⟨_, mem_univ _, Compiler.site_of_reach (reach_input i)⟩

/-- When there are inputs, the graph of the live circuit has a vertex. -/
theorem card_vertex_liveCircuit_pos (hn : 0 < n) :
    0 < Nat.card (Compiler.Vertex (liveCircuit p special)) :=
  have : Nonempty (Compiler.Vertex (liveCircuit p special)) :=
    ⟨.signal ⟨.input ⟨0, hn⟩, reach_input _⟩⟩
  Nat.card_pos

/-- The wires whose vertices lie in `P`. -/
def wiresIn (P : Set (Compiler.Vertex (liveCircuit p special))) : Set (Wire n s) :=
  {w | ∃ hw, (.signal ⟨w, hw⟩ : Compiler.Vertex (liveCircuit p special)) ∈ P}

private def signalWire (w₀ : Compiler.Signal (liveCircuit p special)) : Wire n s := w₀.1

private theorem wiresIn_insert_signal (w₀ : Compiler.Signal (liveCircuit p special))
    (P : Set (Compiler.Vertex (liveCircuit p special))) :
    wiresIn (insert (.signal w₀) P) = insert (signalWire w₀) (wiresIn P) := by
  ext w
  simp only [wiresIn, signalWire, mem_ofPred_eq, mem_insert_iff]
  exact ⟨fun ⟨hw, h⟩ => h.imp (congrArg Subtype.val ∘ Compiler.Vertex.signal.inj) (⟨hw, ·⟩),
    by rintro (rfl | ⟨hw, h⟩); exacts [⟨w₀.2, .inl rfl⟩, ⟨hw, .inr h⟩]⟩

private theorem wiresIn_insert_junction (j : Compiler.Junction (liveCircuit p special))
    (P : Set (Compiler.Vertex (liveCircuit p special))) :
    wiresIn (insert (.junction j) P) = wiresIn P := by
  ext w
  simp [wiresIn]

private theorem wiresIn_insert_output (o : Fin (Nat.card {w // Live p special w}))
    (P : Set (Compiler.Vertex (liveCircuit p special))) :
    wiresIn (insert (.output o) P) = wiresIn P := by
  ext w
  simp [wiresIn]

private theorem notMem_wiresIn_of_signal_notMem {w₀ : Compiler.Signal (liveCircuit p special)}
    {P : Set (Compiler.Vertex (liveCircuit p special))} (h : .signal w₀ ∉ P) :
    signalWire w₀ ∉ wiresIn P :=
  fun ⟨_, hmem⟩ => h hmem

namespace Ledger

variable {I : Interpretation σ U} {M : Type*} [CommMonoid M] (L : Ledger special p I M)

/-- The constraint network of the live circuit on the guess `m`, accepting every value. Its
satisfying assignments are the runs with guess `m`. Its graph and its sites are those of the live
network, whatever the guess. -/
noncomputable abbrev network (m : M) :
    Network U (Fin n) (Compiler.Vertex (liveCircuit p special))
      (Compiler.Edge (liveCircuit p special)) :=
  Compiler.network (liveCircuit p special) (I.withConstants (L.readout m)) fun _ => univ

/-- The run with guess `m` satisfies the network on the guess `m`. -/
private theorem satisfies_network (m : M) (x : Fin n → U) :
    (L.network m).Satisfies x fun e => L.run m x e.signal.1 :=
  Compiler.satisfies_trace fun _ => mem_univ _

/-- A satisfying assignment of the network on the guess `m` is the run with guess `m`. -/
private theorem eq_run_of_satisfies {m : M} {x : Fin n → U}
    {α : Compiler.Edge (liveCircuit p special) → U}
    (h : (L.network m).Satisfies x α) (e : Compiler.Edge (liveCircuit p special)) :
    α e = L.run m x e.signal.1 :=
  Compiler.eq_trace h e

/-- A wire that is not a signal of the live circuit is a constant of the erased program, so its
value in a run depends only on the guess. -/
private theorem run_eq_of_not_reach (m : M) {w : Wire n s}
    (hw : ¬Compiler.Reach (liveCircuit p special) w) (x y : Fin n → U) :
    L.run m x w = L.run m y w := by
  have hlive : ¬Live p special w := mt reach_of_live hw
  cases w with
  | input => exact absurd trivial hlive
  | gate g =>
    by_cases hs : special g
    · rw [L.run_gate_of_special m x hs, L.run_gate_of_special m y hs]
    · have h0 : σ.Arity (p.lines g).op = 0 := Classical.byContradiction fun h => hlive ⟨hs, h⟩
      rw [L.run_gate_of_not_special m x hs, L.run_gate_of_not_special m y hs]
      exact congrArg _ (funext fun a => Fin.elim0 (h0 ▸ a))

omit [DecidablePred special] in
private theorem totalOn_insert {u : Wire n s} {Q : Set (Wire n s)} (hu : u ∉ Q)
    (v : Wire n s → U) :
    L.totalOn (insert u Q) v = L.contribution u (v u) * L.totalOn Q v := by
  classical
  rw [totalOn, totalOn]
  trans ∏ w ∈ insert u (Finset.univ.filter (· ∈ Q)), L.contribution w (v w)
  · exact Finset.prod_congr (by ext; simp) fun _ _ => rfl
  · exact Finset.prod_insert (by simp [hu])

/-! ### Splicing -/

/-- **Splicing traces wire by wire.** If the runs of `x` and `y` have the same readout on the
special gates, the same ledger on the wires of a set of vertices `P`, and the same values on the
edge cut of `P`, then every input `z` that reads like `x` at `P` and like `y` elsewhere has
`p.trace I z` equal to `p.trace I x` on `wiresIn P` and equal to `p.trace I y` outside
`wiresIn P`. -/
theorem trace_of_splice {P : Set (Compiler.Vertex (liveCircuit p special))} {x y z : Fin n → U}
    (hread : L.readout (L.total (p.trace I x)) = L.readout (L.total (p.trace I y)))
    (hpart : L.totalOn (wiresIn P) (p.trace I x) = L.totalOn (wiresIn P) (p.trace I y))
    (hcut : EqOn (fun e => p.trace I x e.signal.1) (fun e => p.trace I y e.signal.1)
      ((liveNetwork p special U).edgeCut P))
    (hzx : EqOn z x ((liveNetwork p special U).readIn P))
    (hzy : EqOn z y ((liveNetwork p special U).readIn P)ᶜ)
    (w : Wire n s) :
    (w ∈ wiresIn P → p.trace I z w = p.trace I x w) ∧
      (w ∉ wiresIn P → p.trace I z w = p.trace I y w) := by
  have hαy := L.run_total_trace y ▸ L.satisfies_network (L.total (p.trace I y)) y
  have hαx : (L.network (L.total (p.trace I y))).Satisfies x fun e => p.trace I x e.signal.1 := by
    simpa only [network, hread, L.run_total_trace] using
      L.satisfies_network (L.total (p.trace I x)) x
  generalize hmdef : L.total (p.trace I y) = m at hαx hαy
  obtain ⟨γ, hγ, hγx, hγy⟩ := hαx.splice hαy hcut hzx hzy
  have hwire (u : Wire n s) : (u ∈ wiresIn P → L.run m z u = p.trace I x u) ∧
      (u ∉ wiresIn P → L.run m z u = p.trace I y u) := by
    by_cases hreach : Compiler.Reach (liveCircuit p special) u
    · rw [← show γ (Compiler.head ⟨u, hreach⟩) = L.run m z u from L.eq_run_of_satisfies hγ _]
      refine ⟨fun ⟨_, hu⟩ => hγx (.inl hu), fun hu => ?_⟩
      by_cases ht : Compiler.head ⟨u, hreach⟩ ∈ (L.network m).touching P
      · exact (hγx ht).trans (hcut (ht.elim (fun h => absurd ⟨hreach, h⟩ hu)
          fun h hiff => hu ⟨hreach, hiff.mpr h⟩))
      · exact hγy ht
    · exact ⟨fun ⟨h, _⟩ => absurd h hreach,
        fun _ => (L.run_eq_of_not_reach m hreach z y).trans
          (hmdef ▸ congrFun (L.run_total_trace y) u)⟩
  have htotal : L.total (L.run m z) = m := calc
    L.total (L.run m z)
      = L.totalOn (wiresIn P) (L.run m z) * L.totalOn (wiresIn P)ᶜ (L.run m z) :=
        L.total_eq_mul (wiresIn P) _
    _ = L.totalOn (wiresIn P) (p.trace I x) * L.totalOn (wiresIn P)ᶜ (p.trace I y) := by
        unfold totalOn
        exact congrArg₂ (· * · : M → M → M)
          (Finset.prod_congr rfl fun u hu =>
            congrArg (L.contribution u) ((hwire u).1 (by simpa using hu)))
          (Finset.prod_congr rfl fun u hu =>
            congrArg (L.contribution u) ((hwire u).2 (by simpa using hu)))
    _ = m := by rw [hpart, ← L.total_eq_mul, hmdef]
  exact L.run_eq_trace htotal ▸ hwire w

/-- **Splicing two inputs with the same message.** Let `x` and `y` be inputs whose value at the
wire `o` lies in `Acc`. If their runs have the same readout on the special gates, the same ledger
on the wires of a set of vertices `P`, and the same values on the edge cut of `P`, then every
input `z` that reads like `x` at `P` and like `y` elsewhere has its value at `o` in `Acc` as
well. -/
theorem mem_of_splice {o : Wire n s} {Acc : Set U}
    {P : Set (Compiler.Vertex (liveCircuit p special))} {x y z : Fin n → U}
    (hx : p.trace I x o ∈ Acc) (hy : p.trace I y o ∈ Acc)
    (hread : L.readout (L.total (p.trace I x)) = L.readout (L.total (p.trace I y)))
    (hpart : L.totalOn (wiresIn P) (p.trace I x) = L.totalOn (wiresIn P) (p.trace I y))
    (hcut : EqOn (fun e => p.trace I x e.signal.1) (fun e => p.trace I y e.signal.1)
      ((liveNetwork p special U).edgeCut P))
    (hzx : EqOn z x ((liveNetwork p special U).readIn P))
    (hzy : EqOn z y ((liveNetwork p special U).readIn P)ᶜ) :
    p.trace I z o ∈ Acc := by
  have hwire := L.trace_of_splice hread hpart hcut hzx hzy o
  by_cases ho : o ∈ wiresIn P
  · exact hwire.1 ho ▸ hx
  · exact hwire.2 ho ▸ hy

/-- **Locality inside a closed set.** For a fixed guess, the values of the run on the edges at a
closed set of vertices `W` depend only on the inputs read in `W`. -/
theorem run_eq_of_eqOn_readIn (m : M) {W : Set (Compiler.Vertex (liveCircuit p special))}
    (hW : (liveNetwork p special U).edgeCut W = ∅) {x x' : Fin n → U}
    (hxx' : EqOn x x' ((liveNetwork p special U).readIn W))
    {e : Compiler.Edge (liveCircuit p special)} (he : e ∈ (liveNetwork p special U).touching W) :
    L.run m x e.signal.1 = L.run m x' e.signal.1 := by
  have hW' : (L.network m).edgeCut W = ∅ := hW
  obtain ⟨γ, hγ, hγx, -⟩ := (L.satisfies_network m x).splice (L.satisfies_network m x')
    (by rw [hW']; exact eqOn_empty _ _) hxx'.symm (eqOn_refl _ _)
  rw [← L.eq_run_of_satisfies hγ e]
  exact (hγx he).symm

/-! ### The sweep -/

section Sweep

variable (o : Wire n s) (Acc : Set U) (π : Layout (Compiler.Vertex (liveCircuit p special)))

/-- The extra message at time `t`: the readout of the consistent guess on the special gates and
the ledger of the first `t` vertices. After the last vertex it is constant. -/
noncomputable def extra (t : ℕ) (x : Fin n → U) : ({g // special g} → U) × M :=
  if t ≤ Nat.card (Compiler.Vertex (liveCircuit p special)) then
    (L.readout (L.total (p.trace I x)), L.totalOn (wiresIn (π.initial t)) (p.trace I x))
  else (L.readout 1, 1)

/-- **The sweep of a program with a ledger**, along a layout of its live network: the frontier
sweep of the values of the run, whose extra message is the readout on the special gates and the
ledger so far. -/
noncomputable def sweep : Sweep {x | p.trace I x o ∈ Acc}
    ((({g // special g} → U) × M) × (Compiler.Edge (liveCircuit p special) → Option U)) :=
  (liveNetwork p special U).frontierSweep π (fun x e => p.trace I x e.signal.1) (L.extra π)
    (fun _ _ _ _ => by simp [extra])
    fun t ht x hx y hy hxy hval z hzx hzy => by
      simp only [extra, ht, ↓reduceIte, Prod.mk.injEq] at hxy
      exact L.mem_of_splice hx hy hxy.1 hxy.2 hval hzx hzy

variable {o Acc}

/-- When step `t` processes vertex `v`, `L.extra π (t + 1)` is determined by `L.extra π t` and, if
`v = .signal w₀`, the value of the run at `w₀`. -/
theorem extra_succ_eq {t : ℕ} (ht : t < Nat.card (Compiler.Vertex (liveCircuit p special)))
    {x y : Fin n → U} (h₀ : L.extra π t x = L.extra π t y)
    (hw : ∀ w₀ : Compiler.Signal (liveCircuit p special),
      π.symm ⟨t, ht⟩ = .signal w₀ → p.trace I x w₀.1 = p.trace I y w₀.1) :
    L.extra π (t + 1) x = L.extra π (t + 1) y := by
  simp only [extra, ht.le, show t + 1 ≤ _ from ht, ↓reduceIte, Prod.mk.injEq] at h₀ ⊢
  refine ⟨h₀.1, ?_⟩
  rw [π.initial_succ ht]
  cases hv : π.symm ⟨t, ht⟩ with
  | signal w₀ =>
    have hnot : signalWire w₀ ∉ wiresIn (π.initial t) :=
      notMem_wiresIn_of_signal_notMem (hv ▸ by simp [Layout.mem_initial])
    rw [wiresIn_insert_signal, L.totalOn_insert hnot, L.totalOn_insert hnot]
    dsimp only [signalWire]
    rw [hw w₀ hv, h₀.2]
  | junction => rw [wiresIn_insert_junction, h₀.2]
  | output => rw [wiresIn_insert_output, h₀.2]

private theorem head_mem_frontier_union {t : ℕ}
    (ht : t < Nat.card (Compiler.Vertex (liveCircuit p special)))
    {w₀ : Compiler.Signal (liveCircuit p special)} (hv : π.symm ⟨t, ht⟩ = .signal w₀) :
    Compiler.head w₀ ∈ (liveNetwork p special U).frontier π t ∪
      (liveNetwork p special U).frontier π (t + 1) := by
  set G := liveNetwork p special U
  have hsrc : G.src (Compiler.head w₀) = π.symm ⟨t, ht⟩ := hv.symm
  have hv_not : π.symm ⟨t, ht⟩ ∉ π.initial t := by simp [Layout.mem_initial]
  by_cases htgt : G.tgt (Compiler.head w₀) ∈ π.initial t
  · exact .inl fun h => hv_not (hsrc ▸ h.mpr htgt)
  · refine .inr ?_
    rw [Multigraph.frontier, π.initial_succ ht]
    exact fun h => (mem_insert_iff.mp (h.mp (hsrc ▸ mem_insert _ _))).elim
      (hsrc ▸ (Compiler.loopless (Compiler.head w₀)).symm) htgt

/-- The extra message at time `t` takes at most `min (|U| ^ k) |M| * |M|` values, where `k` is the
number of special gates: the readout lies in `{g // special g} → U` as well as in the image of `M`,
and the partial ledger lies in `M`. -/
theorem ncard_extra_le [Finite U] [Finite M] (t : ℕ) :
    (L.extra π t '' {x | p.trace I x o ∈ Acc}).ncard ≤
      min (Nat.card U ^ Nat.card {g // special g}) (Nat.card M) * Nat.card M := by
  have hpow : (L.extra π t '' {x | p.trace I x o ∈ Acc}).ncard ≤
      Nat.card U ^ Nat.card {g // special g} * Nat.card M :=
    (ncard_le_card _).trans_eq (by rw [Nat.card_prod, Nat.card_fun])
  have hsq : (L.extra π t '' {x | p.trace I x o ∈ Acc}).ncard ≤ Nat.card M * Nat.card M :=
    (ncard_image_le_ncard_image_of_factorsThrough (g := fun x =>
        (L.total (p.trace I x), L.totalOn (wiresIn (π.initial t)) (p.trace I x))) (toFinite _)
      fun x _ y _ hxy => by simp only [Prod.mk.injEq] at hxy; simp only [extra, hxy.1, hxy.2]).trans
      ((ncard_le_card _).trans_eq (Nat.card_prod _ _))
  rcases le_total (Nat.card U ^ Nat.card {g // special g}) (Nat.card M) with hle | hle <;>
    [rwa [min_eq_left hle]; rwa [min_eq_right hle]]

/-- **Transitions by width.** A transition at step `t` is determined by the extra message at time
`t`, the values on the two frontiers, and the input read at the vertex processed. -/
theorem ncard_transition_le_width [Finite U] [Finite M] {t : ℕ}
    (ht : t < Nat.card (Compiler.Vertex (liveCircuit p special))) :
    ((L.sweep o Acc π).transition t '' {x | p.trace I x o ∈ Acc}).ncard ≤
      (min (Nat.card U ^ Nat.card {g // special g}) (Nat.card M) * Nat.card M) *
        Nat.card U ^ (((liveNetwork p special U).frontier π t ∪
          (liveNetwork p special U).frontier π (t + 1)).ncard +
            ((liveNetwork p special U).readAt (π.symm ⟨t, ht⟩)).ncard) := by
  set G := liveNetwork p special U
  set C := G.frontier π t ∪ G.frontier π (t + 1)
  set Q := G.readAt (π.symm ⟨t, ht⟩)
  have h := (L.sweep o Acc π).ncard_transition_le_of_factorsThrough (t := t)
    (D := (C → U) × (Q → U)) (L.extra π t)
    (fun x => (C.domRestrict (fun e => p.trace I x e.signal.1), Q.domRestrict x))
    fun x _ y _ h₀ hg => by
      simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at hg
      have hsucc : L.extra π (t + 1) x = L.extra π (t + 1) y :=
        L.extra_succ_eq π ht h₀ fun w₀ hv => hg.1 (head_mem_frontier_union π ht hv)
      simp only [Sweep.transition, sweep, Network.frontierSweep, Prod.mk.injEq,
        Network.frontierValues_eq_iff, domRestrict_eq_domRestrict_iff]
      exact ⟨⟨h₀, hg.1.mono subset_union_left⟩, ⟨hsucc, hg.1.mono subset_union_right⟩,
        hg.2.mono (G.revealedBy_succ_diff_subset π ht)⟩
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    ← pow_add] at h
  exact h.trans (Nat.mul_le_mul_right _ (L.ncard_extra_le π t))

/-- **Transitions inside a closed set.** If the vertex processed at step `t` lies in a closed
set `W` whose edges contain both frontiers of the step, a transition is determined by the extra
message at time `t` and the inputs read in `W`. -/
theorem ncard_transition_le_readIn [Finite U] [Finite M] {t : ℕ}
    (ht : t < Nat.card (Compiler.Vertex (liveCircuit p special)))
    {W : Set (Compiler.Vertex (liveCircuit p special))}
    (hW : (liveNetwork p special U).edgeCut W = ∅) (hv : π.symm ⟨t, ht⟩ ∈ W)
    (hC : (liveNetwork p special U).frontier π t ∪ (liveNetwork p special U).frontier π (t + 1) ⊆
      (liveNetwork p special U).touching W) :
    ((L.sweep o Acc π).transition t '' {x | p.trace I x o ∈ Acc}).ncard ≤
      (min (Nat.card U ^ Nat.card {g // special g}) (Nat.card M) * Nat.card M) *
        Nat.card U ^ ((liveNetwork p special U).readIn W).ncard := by
  set G := liveNetwork p special U
  set Q := G.readIn W
  have h := (L.sweep o Acc π).ncard_transition_le_of_factorsThrough (t := t) (D := Q → U)
    (L.extra π t) (fun x => Q.domRestrict x) fun x _ y _ h₀ hg => by
      rw [domRestrict_eq_domRestrict_iff] at hg
      have hread : L.readout (L.total (p.trace I x)) = L.readout (L.total (p.trace I y)) := by
        simpa only [extra, ht.le, ↓reduceIte] using congrArg Prod.fst h₀
      have hval : EqOn (fun e => p.trace I x e.signal.1) (fun e => p.trace I y e.signal.1)
          (G.touching W) := fun e he => by
        change p.trace I x e.signal.1 = p.trace I y e.signal.1
        rw [← L.run_total_trace x, ← L.run_total_trace y,
          ← show L.run (L.total (p.trace I x)) y = L.run (L.total (p.trace I y)) y by
            rw [run, run, hread]]
        exact L.run_eq_of_eqOn_readIn _ hW hg he
      have hsucc := L.extra_succ_eq π ht h₀ fun w₀ hvw₀ =>
        @hval (Compiler.head w₀) (.inl (show Compiler.Vertex.signal w₀ ∈ W from hvw₀ ▸ hv))
      simp only [Sweep.transition, sweep, Network.frontierSweep, Prod.mk.injEq,
        Network.frontierValues_eq_iff, domRestrict_eq_domRestrict_iff]
      exact ⟨⟨h₀, hval.mono (subset_union_left.trans hC)⟩,
        ⟨hsucc, hval.mono (subset_union_right.trans hC)⟩,
        fun i hi => hg ⟨_, hv, G.revealedBy_succ_diff_subset π ht hi⟩⟩
  exact h.trans (Nat.mul_le_mul (L.ncard_extra_le π t)
    (by rw [Nat.card_fun, Nat.card_coe_set_eq]))

/-- At the last step `L.extra π (|V| + 1)` is constant and every input has been read, so the
transition is determined by `L.extra π |V|`. -/
private theorem ncard_transition_last_le [Finite U] [Finite M] :
    ((L.sweep o Acc π).transition (Nat.card (Compiler.Vertex (liveCircuit p special))) ''
      {x | p.trace I x o ∈ Acc}).ncard ≤
        min (Nat.card U ^ Nat.card {g // special g}) (Nat.card M) * Nat.card M := by
  let V := Nat.card (Compiler.Vertex (liveCircuit p special))
  have h : ((L.sweep o Acc π).transition V '' {x | p.trace I x o ∈ Acc}).ncard ≤
      ((fun x => (L.extra π V x, L.extra π (V + 1) x)) ''
          {x | p.trace I x o ∈ Acc}).ncard * Nat.card U ^ (liveNetwork p special U).readᶜ.ncard :=
    (liveNetwork p special U).ncard_transition_last_le
  have hextra : ((fun x => (L.extra π V x, L.extra π (V + 1) x)) ''
      {x | p.trace I x o ∈ Acc}).ncard ≤
      min (Nat.card U ^ Nat.card {g // special g}) (Nat.card M) * Nat.card M :=
    (ncard_image_le_ncard_image_of_factorsThrough (g := L.extra π V) (toFinite _)
      fun _ _ _ _ hxy => Prod.ext hxy (by simp [extra, V])).trans (L.ncard_extra_le π V)
  simpa [read_liveNetwork] using h.trans (Nat.mul_le_mul_right _ hextra)

include L in
/-- **Counting along a layout of the components.** Suppose that, at each step of a layout, the
frontiers lie among the edges of the component of the vertex processed. Then some step `t`
bounds the set accepted by `p` by
`(K - 1) ^ 2 (|V| + 1) (min (|U| ^ k) |M| * |M|) q ^ e`, where `q = |U|`, `k` counts the special
gates, and `e` is the smaller of the width of the step and the number of inputs read in the
component of the vertex processed. -/
theorem exists_ncard_le [Finite U] [Nonempty U] [Finite M] {K : ℕ}
    (hfree : RectangleFree {x | p.trace I x o ∈ Acc} K)
    (hK : K ≤ {x | p.trace I x o ∈ Acc}.ncard)
    (hV : 0 < Nat.card (Compiler.Vertex (liveCircuit p special)))
    (hC : ∀ t (ht : t < Nat.card (Compiler.Vertex (liveCircuit p special))),
      (liveNetwork p special U).frontier π t ∪ (liveNetwork p special U).frontier π (t + 1) ⊆
        (liveNetwork p special U).touching
          ((liveNetwork p special U).component (π.symm ⟨t, ht⟩))) :
    ∃ t, ∃ ht : t < Nat.card (Compiler.Vertex (liveCircuit p special)),
      {x | p.trace I x o ∈ Acc}.ncard ≤
        (K - 1) ^ 2 * (Nat.card (Compiler.Vertex (liveCircuit p special)) + 1) *
          (min (Nat.card U ^ Nat.card {g // special g}) (Nat.card M) * Nat.card M) *
            Nat.card U ^ min (((liveNetwork p special U).frontier π t ∪
              (liveNetwork p special U).frontier π (t + 1)).ncard +
                ((liveNetwork p special U).readAt (π.symm ⟨t, ht⟩)).ncard)
              ((liveNetwork p special U).readIn
                ((liveNetwork p special U).component (π.symm ⟨t, ht⟩))).ncard := by
  set S := {x | p.trace I x o ∈ Acc}
  set N := Nat.card (Compiler.Vertex (liveCircuit p special))
  set G := liveNetwork p special U
  set E := min (Nat.card U ^ Nat.card {g // special g}) (Nat.card M) * Nat.card M
  have hq : 1 ≤ Nat.card U := Nat.card_pos
  -- The exponent at each step: the smaller of its width and the inputs of its component.
  let f : ℕ → ℕ := fun t => if ht : t < N then
    min ((G.frontier π t ∪ G.frontier π (t + 1)).ncard + (G.readAt (π.symm ⟨t, ht⟩)).ncard)
      (G.readIn (G.component (π.symm ⟨t, ht⟩))).ncard else 0
  obtain ⟨t, htmem, hmax⟩ := Finset.exists_max_image (Finset.range N) f
    ⟨0, Finset.mem_range.mpr hV⟩
  have ht : t < N := Finset.mem_range.mp htmem
  refine ⟨t, ht, ?_⟩
  have hstep : ∀ t' ∈ Finset.range (N + 1),
      ((L.sweep o Acc π).transition t' '' S).ncard ≤ E * Nat.card U ^ f t := by
    intro t' ht'mem
    rcases Nat.lt_or_ge t' N with ht' | ht'
    · calc ((L.sweep o Acc π).transition t' '' S).ncard
          ≤ E * Nat.card U ^ f t' := by
            simp only [f, ht', ↓reduceDIte]
            rcases min_cases ((G.frontier π t' ∪ G.frontier π (t' + 1)).ncard +
                (G.readAt (π.symm ⟨t', ht'⟩)).ncard)
              (G.readIn (G.component (π.symm ⟨t', ht'⟩))).ncard with
              ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
            · exact L.ncard_transition_le_width π ht'
            · exact L.ncard_transition_le_readIn π ht' (G.edgeCut_component _)
                (G.mem_component_self _) (hC t' ht')
        _ ≤ E * Nat.card U ^ f t :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq (hmax t' (Finset.mem_range.mpr ht')))
    · obtain rfl : t' = N := by have := Finset.mem_range.mp ht'mem; omega
      exact (L.ncard_transition_last_le π).trans
        (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  have hft : f t = min ((G.frontier π t ∪ G.frontier π (t + 1)).ncard +
      (G.readAt (π.symm ⟨t, ht⟩)).ncard) (G.readIn (G.component (π.symm ⟨t, ht⟩))).ncard := by
    simp only [f, ht, ↓reduceDIte]
  calc S.ncard ≤ (K - 1) ^ 2 * ∑ t ∈ Finset.range (N + 1),
        ((L.sweep o Acc π).transition t '' S).ncard := (L.sweep o Acc π).ncard_le hfree hK
    _ ≤ (K - 1) ^ 2 * ((N + 1) * (E * Nat.card U ^ f t)) := by
        gcongr
        simpa using Finset.sum_le_card_nsmul (Finset.range (N + 1)) _ _ hstep
    _ = _ := by rw [← hft]; ring

end Sweep

end Ledger

end Cslib.Circuits.Frontier
