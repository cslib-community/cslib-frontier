/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.DescriptorCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Linear circuits: Kirchhoff semantics, modified nodal equations and certified stability

## The component language

A netlist (`Cslib.Electrical.Netlist`) has `nodes` numbered `1, …, nodes`, with node `0` the
ground (datum), `inputs` input ports, and a list of two-terminal branches
(`Cslib.Electrical.Branch`), each with a positive terminal `pos`, a negative terminal `neg` and
an element (`Cslib.Electrical.Element`). Values are exact rationals in SI units: potentials and
voltages in volts, currents in amperes, time in seconds.

* `resistor R` (ohms), `capacitor C` (farads), `inductor L` (henries): linear, `R, C, L > 0`.
* `voltageSource E input` (volts), `currentSource J input` (amperes): an independent source of
  constant value `E` (`J`), plus the input signal `u_k` when `input = some k`.
* `vccs g cp cn` (siemens): the branch current is `g (φ_cp - φ_cn)`.
* `vcvs μ cp cn` (dimensionless): the branch voltage is `μ (φ_cp - φ_cn)`.

Branch `b` has voltage `v_b = φ_pos - φ_neg`, with `φ_0 = 0`, and current `i_b` flowing from
`pos` through the element to `neg` (passive sign convention); a source supplying power has
`v_b i_b < 0`. `Netlist.check` rejects a netlist that names a node above `nodes`, an input port
at or above `inputs`, or a nonpositive `R`, `C` or `L`. No other element (diodes, transistors,
switches, mutual inductance, current-controlled sources, nonlinear or time-varying values) is in
the language.

## Kirchhoff semantics

`Netlist.IsTrajectoryOn c u φ i s` is the semantic definition, on a time set `s`: node potentials
`φ t` and branch currents `i t` such that, at every `t ∈ s`,

* **KCL**: the currents leaving each non-ground node through its branches sum to zero;
* **KVL**, through the potentials: each branch voltage is `φ_pos - φ_neg`;
* the **element laws**: `v = R i`; `v' = i / C` (`i = C v'`); `i' = v / L` (`v = L i'`);
  `v = E + u_k`; `i = J + u_k`; `i = g v_c`; `v = μ v_c`.

Only capacitor voltages and inductor currents are required to be differentiable.

## Modified nodal equations

The unknowns are the node potentials followed by **all** branch currents, `z = (φ, i)` with
`N = nodes + #branches` entries (`Fin.append`). The equations are KCL at each non-ground node
followed by one equation per branch, its element law written with `v_b = φ_pos - φ_neg`:
`E ż = F z + G u + b` (`Netlist.mna`). This is modified nodal analysis with every branch current
kept as an unknown (Hachtel's sparse tableau with the branch voltages eliminated by KVL); the
classical MNA, which eliminates resistor, capacitor, current-source and VCCS currents, is one of
the eliminations that a decoupling certificate may perform. `E` is singular whenever the circuit
has a branch that is not a capacitor or inductor, and nothing assumes otherwise.

`Netlist.isTrajectoryOn_iff` proves that the circuit trajectories are exactly the solutions of
the descriptor system: `(φ, i)` is a trajectory if and only if `Fin.append φ i` solves
`E ż = F z + G u + b`.

## Certified stability and realizations

`Netlist.isExponentiallyStable_of_check` composes the semantics with the exact checkers of
`CslibFrontier.Algorithms.LinearAlgebra.DescriptorCertificate`: a well-formed netlist, an
accepted index-one decoupling of its equations, an exactly checked equilibrium `z₀` and
exponential stability of the checked reduced matrix (for instance from an accepted dense or
sparse Lyapunov certificate) together prove that

* `z₀` is a circuit trajectory (the DC operating point),
* every differential state `x₀` (one coordinate per independent capacitor voltage or inductor
  current, after the decoupling) starts a circuit trajectory, and
* every circuit trajectory with zero input converges to `z₀` exponentially: all potentials and
  all branch currents, in the Euclidean norm of the full vector.

The supported class is the circuits whose equations have an index-one decoupling; nothing is
claimed for any other circuit. By DAE index theory, loops of capacitors and voltage sources,
cutsets of inductors and current sources, inconsistent sources and underdetermined subcircuits
have none; this characterization is not proved here, but acceptance implies existence and
uniqueness, so a circuit without trajectories, or with fewer than a decoupling would give, has no
accepted certificate (the tests prove this for an inconsistent and an index-two circuit). Failure
to find a certificate is not an instability proof.

`Netlist.isTrajectoryOn_iff_realization` gives, for selected output probes
(`Cslib.Electrical.Probe`: a node-pair voltage or a branch current) and the input ports, the
proper realization `ẋ = A x + B u`, `y - y₀ = C x + D u` after the equilibrium shift, on every
time set with unique derivatives and for every input signal, including direct feedthrough `D`.
No derivative of the input appears; an elimination that would need one has no index-one
decoupling.

## Main definitions

* `Cslib.Electrical.Element`, `Cslib.Electrical.Branch`, `Cslib.Electrical.Netlist`,
  `Cslib.Electrical.Probe`.
* `Cslib.Electrical.Netlist.check`, `Cslib.Electrical.Probe.check`: well-formedness of a netlist
  and of a probe (1-based nodes, 0-based branch positions).
* `Cslib.Electrical.Netlist.IsTrajectoryOn`: Kirchhoff semantics.
* `Cslib.Electrical.Netlist.eRows`, `fRows`, `gRows`, `bList`, `probeRows`: the rational
  modified nodal equations, computed by the kernel; `Netlist.mna` is their real descriptor
  system.

## Main results

* `Cslib.Electrical.Netlist.isTrajectoryOn_iff`: circuit trajectories are exactly the solutions
  of the modified nodal equations.
* `Cslib.Electrical.Netlist.probeRows_mulVec`: the probe rows compute the probed quantities.
* `Cslib.Electrical.Netlist.isExponentiallyStable_of_check`: end-to-end certified exponential
  stability of every trajectory about the checked operating point, with existence.
* `Cslib.Electrical.Netlist.isTrajectoryOn_iff_realization`: the checked proper realization for
  selected inputs and outputs.
-/

public section

open Set Matrix Mathlib.Tactic.Matrix Cslib.LinearAlgebra

namespace Cslib.Electrical

/-- A circuit element. Values are exact rationals in SI units; see the module documentation for
the element laws and sign conventions. -/
inductive Element where
  /-- A linear resistor of resistance `R` ohms: `v = R i`. -/
  | resistor (R : ℚ)
  /-- A linear capacitor of capacitance `C` farads: `i = C v'`. -/
  | capacitor (C : ℚ)
  /-- A linear inductor of inductance `L` henries: `v = L i'`. -/
  | inductor (L : ℚ)
  /-- An independent voltage source `v = E + u_k` (volts), with `u_k = 0` for `input = none`. -/
  | voltageSource (E : ℚ) (input : Option ℕ)
  /-- An independent current source `i = J + u_k` (amperes). -/
  | currentSource (J : ℚ) (input : Option ℕ)
  /-- A voltage-controlled current source `i = g (φ_cp - φ_cn)`, `g` in siemens. -/
  | vccs (g : ℚ) (cp cn : ℕ)
  /-- A voltage-controlled voltage source `v = μ (φ_cp - φ_cn)`. -/
  | vcvs (μ : ℚ) (cp cn : ℕ)
  deriving Inhabited

/-- A two-terminal branch: its current flows from `pos` through the element to `neg`. Node `0`
is ground. -/
structure Branch where
  /-- The positive terminal. -/
  pos : ℕ
  /-- The negative terminal. -/
  neg : ℕ
  /-- The element. -/
  elem : Element
  deriving Inhabited

/-- A netlist with non-ground nodes `1, …, nodes`, `inputs` input ports and its branches. -/
structure Netlist where
  /-- The number of non-ground nodes. -/
  nodes : ℕ
  /-- The number of input ports. -/
  inputs : ℕ
  /-- The branches. -/
  branches : List Branch

/-- An output probe: the voltage `φ_p - φ_q`, or the current of a branch.

Nodes and branches are indexed differently. Nodes are **1-based**: `p, q ∈ {0, 1, …, nodes}`,
with `0` the ground. Branches are **0-based**: `b ∈ {0, …, branches.length - 1}` is the position
of the branch in `Netlist.branches`. An out-of-range probe evaluates to `0` (`Probe.eval`,
`Netlist.probeRows`); `Probe.check` rejects it. -/
inductive Probe where
  /-- The voltage `φ_p - φ_q` between nodes `p` and `q` (1-based, `0` is ground). -/
  | voltage (p q : ℕ)
  /-- The current of branch `b` (0-based position in `Netlist.branches`). -/
  | current (b : ℕ)

/-! ### Well-formedness -/

namespace Element

/-- Whether the element's parameters and references are supported for a netlist with `n` nodes
and `m` inputs. -/
@[expose] def check (n m : ℕ) : Element → Bool
  | resistor R => 0 < R
  | capacitor C => 0 < C
  | inductor L => 0 < L
  | voltageSource _ input => input.all (· < m)
  | currentSource _ input => input.all (· < m)
  | vccs _ cp cn => cp ≤ n && cn ≤ n
  | vcvs _ cp cn => cp ≤ n && cn ≤ n

end Element

namespace Netlist

variable (c : Netlist)

/-- Whether every branch refers to existing nodes and inputs and has supported parameters. -/
@[expose] def check : Bool :=
  c.branches.all fun br => br.pos ≤ c.nodes && br.neg ≤ c.nodes && br.elem.check c.nodes c.inputs

/-- The number of unknowns of the modified nodal equations: potentials, then branch currents. -/
abbrev size : ℕ := c.nodes + c.branches.length

end Netlist

/-- Whether a probe refers to existing nodes (`≤ nodes`, 1-based with ground `0`) or an existing
branch (`< branches.length`, 0-based). -/
@[expose] def Probe.check (c : Netlist) : Probe → Bool
  | .voltage p q => p ≤ c.nodes && q ≤ c.nodes
  | .current b => b < c.branches.length

/-! ### Kirchhoff semantics -/

/-- The potential of node `k`: `0` for the ground `k = 0`, and `φ (k - 1)` for `1 ≤ k ≤ n`. (A
well-formed netlist names no other node.) -/
@[expose] def potential {n : ℕ} (φ : Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : k ≠ 0 ∧ k - 1 < n then φ ⟨k - 1, h.2⟩ else 0

/-- The value of an input port, `0` for `none`. -/
@[expose] def inputValue {m : ℕ} (w : Fin m → ℝ) : Option ℕ → ℝ
  | none => 0
  | some k => if h : k < m then w ⟨k, h⟩ else 0

/-- `1` if branch `br` leaves node `k`, `-1` if it enters it, `0` otherwise (or for a self
loop). -/
@[expose] def Branch.incidence (br : Branch) (k : ℕ) : ℚ :=
  (if br.pos = k then 1 else 0) - (if br.neg = k then 1 else 0)

/-- The law of an element at time `t`, for its branch voltage `v`, its branch current `i`, the
node potentials `φ` (for controlled sources) and the input `w`. -/
@[expose] def Element.Law {n m : ℕ} (v i : ℝ → ℝ) (φ : ℝ → Fin n → ℝ) (w : ℝ → Fin m → ℝ)
    (s : Set ℝ) (t : ℝ) : Element → Prop
  | resistor R => v t = R * i t
  | capacitor C => HasDerivWithinAt v (i t / C) s t
  | inductor L => HasDerivWithinAt i (v t / L) s t
  | voltageSource E input => v t = E + inputValue (w t) input
  | currentSource J input => i t = J + inputValue (w t) input
  | vccs g cp cn => i t = g * (potential (φ t) cp - potential (φ t) cn)
  | vcvs μ cp cn => v t = μ * (potential (φ t) cp - potential (φ t) cn)

namespace Netlist

variable (c : Netlist)

/-- **Kirchhoff semantics.** Node potentials `φ` and branch currents `i` form a trajectory of the
circuit with input `u` on the time set `s`: KCL holds at every non-ground node and every branch
obeys its element law, with branch voltage `φ_pos - φ_neg`. -/
structure IsTrajectoryOn (u : ℝ → Fin c.inputs → ℝ) (φ : ℝ → Fin c.nodes → ℝ)
    (i : ℝ → Fin c.branches.length → ℝ) (s : Set ℝ) : Prop where
  /-- Kirchhoff's current law at node `k + 1`. -/
  kcl : ∀ t ∈ s, ∀ k : Fin c.nodes,
    ∑ b, ((c.branches.get b).incidence (k + 1) : ℝ) * i t b = 0
  /-- The element law of each branch. -/
  law : ∀ t ∈ s, ∀ b, (c.branches.get b).elem.Law
    (fun τ => potential (φ τ) (c.branches.get b).pos - potential (φ τ) (c.branches.get b).neg)
    (fun τ => i τ b) φ u s t

end Netlist

/-! ### Stamps and the modified nodal equations -/

/-- The coefficients of an element's equation `d/dt (eV v + eI i) = fV v + fI i + fC v_c + src
+ u_input`, with `v_c = φ_cp - φ_cn`. -/
structure Stamp where
  /-- The coefficient of the branch voltage under the derivative. -/
  eV : ℚ := 0
  /-- The coefficient of the branch current under the derivative. -/
  eI : ℚ := 0
  /-- The coefficient of the branch voltage. -/
  fV : ℚ := 0
  /-- The coefficient of the branch current. -/
  fI : ℚ := 0
  /-- The coefficient of the control voltage. -/
  fC : ℚ := 0
  /-- The positive control node. -/
  cp : ℕ := 0
  /-- The negative control node. -/
  cn : ℕ := 0
  /-- The constant source value. -/
  src : ℚ := 0
  /-- The input port added to the source value. -/
  input : Option ℕ := none

/-- The stamp of an element. -/
@[expose] def Element.stamp : Element → Stamp
  | resistor R => { fV := 1, fI := -R }
  | capacitor C => { eV := C, fI := 1 }
  | inductor L => { eI := L, fV := 1 }
  | voltageSource E input => { fV := -1, src := E, input := input }
  | currentSource J input => { fI := -1, src := J, input := input }
  | vccs g cp cn => { fI := -1, fC := g, cp := cp, cn := cn }
  | vcvs μ cp cn => { fV := -1, fC := μ, cp := cp, cn := cn }

/-- Column `j` of the row vector of the voltage `φ_p - φ_q`, with `n` potential columns. -/
@[expose] def vrow (n p q j : ℕ) : ℚ :=
  if j < n then (if p = j + 1 then 1 else 0) - (if q = j + 1 then 1 else 0) else 0

/-- Column `j` of the row vector of the current of branch `b`. -/
@[expose] def crow (n b j : ℕ) : ℚ := if j = n + b then 1 else 0

/-- The rows `f i j` for `i < a`, `j < b`. -/
@[expose] def rowsOf (a b : ℕ) (f : ℕ → ℕ → ℚ) : List (List ℚ) :=
  (List.range a).map fun i => (List.range b).map fun j => f i j

private theorem getD_rowsOf {a b : ℕ} (f : ℕ → ℕ → ℚ) {i j : ℕ} (hi : i < a) (hj : j < b) :
    ((rowsOf a b f).getD i []).getD j 0 = f i j := by
  simp [rowsOf, List.getD_eq_getElem?_getD, hi, hj]

private theorem realOfRows_rowsOf_apply {a b : ℕ} (f : ℕ → ℕ → ℚ) (i : Fin a) (j : Fin b) :
    realOfRows a b (rowsOf a b f) i j = (f i j : ℝ) := by
  rw [realOfRows, map_apply, ofLists_apply, ofList_apply, getD_rowsOf f i.is_lt j.is_lt]

/-- Entry `j` of the row of a probe. -/
@[expose] def Probe.entry (n : ℕ) : Probe → ℕ → ℚ
  | .voltage p q => vrow n p q
  | .current b => crow n b

namespace Netlist

variable (c : Netlist)

/-- The branch with index `b` (`default` beyond the list). -/
@[expose] def branch (b : ℕ) : Branch := c.branches.getD b default

/-- Entry `(r, j)` of `E`. -/
@[expose] def eEntry (r j : ℕ) : ℚ :=
  if r < c.nodes then 0 else
    let br := c.branch (r - c.nodes)
    br.elem.stamp.eV * vrow c.nodes br.pos br.neg j +
      br.elem.stamp.eI * crow c.nodes (r - c.nodes) j

/-- Entry `(r, j)` of `F`: `-incidence` in the KCL rows, the stamp in the branch rows. -/
@[expose] def fEntry (r j : ℕ) : ℚ :=
  if r < c.nodes then (if c.nodes ≤ j then -(c.branch (j - c.nodes)).incidence (r + 1) else 0)
  else
    let br := c.branch (r - c.nodes)
    br.elem.stamp.fV * vrow c.nodes br.pos br.neg j +
      br.elem.stamp.fI * crow c.nodes (r - c.nodes) j +
      br.elem.stamp.fC * vrow c.nodes br.elem.stamp.cp br.elem.stamp.cn j

/-- Entry `(r, q)` of `G`. -/
@[expose] def gEntry (r q : ℕ) : ℚ :=
  if r < c.nodes then 0 else if (c.branch (r - c.nodes)).elem.stamp.input = some q then 1 else 0

/-- Entry `r` of `b`. -/
@[expose] def bEntry (r : ℕ) : ℚ :=
  if r < c.nodes then 0 else (c.branch (r - c.nodes)).elem.stamp.src

/-- The rows of `E`. -/
@[expose] def eRows : List (List ℚ) := rowsOf c.size c.size c.eEntry
/-- The rows of `F`. -/
@[expose] def fRows : List (List ℚ) := rowsOf c.size c.size c.fEntry
/-- The rows of `G`. -/
@[expose] def gRows : List (List ℚ) := rowsOf c.size c.inputs c.gEntry
/-- The entries of `b`. -/
@[expose] def bList : List ℚ := (List.range c.size).map c.bEntry

/-- The modified nodal equations `E ż = F z + G u + b` over `ℝ`. -/
@[expose] noncomputable def mna : DescriptorSystem (Fin c.size) (Fin c.inputs) :=
  descriptorOfRows c.size c.inputs c.eRows c.fRows c.gRows c.bList

/-- The rows of the output map `H` of a list of probes. -/
@[expose] def probeRows (probes : List Probe) : List (List ℚ) :=
  rowsOf probes.length c.size fun o j => ((probes.getD o (.current 0)).entry c.nodes) j

end Netlist

/-- The value of a probe for potentials `φ` and branch currents `i`. -/
@[expose] def Probe.eval {n nb : ℕ} (φ : Fin n → ℝ) (i : Fin nb → ℝ) : Probe → ℝ
  | .voltage p q => potential φ p - potential φ q
  | .current b => if h : b < nb then i ⟨b, h⟩ else 0

/-! ### Row computations -/

section Rows

variable {n nb : ℕ} (φ : Fin n → ℝ) (i : Fin nb → ℝ)

private theorem sum_indicator_eq_potential (p : ℕ) :
    ∑ j : Fin n, ((if p = j.val + 1 then 1 else 0 : ℚ) : ℝ) * φ j = potential φ p := by
  unfold potential
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨p - 1, h.2⟩]
    · have hp : (if p = (⟨p - 1, h.2⟩ : Fin n).val + 1 then (1 : ℚ) else 0) = 1 := by
        simp only [ite_eq_left_iff, zero_ne_one, imp_false, not_not]; omega
      rw [hp, Rat.cast_one, one_mul]
    · intro j _ hj
      have : p ≠ j.val + 1 := fun hp => hj (Fin.ext (by simp; omega))
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    have : p ≠ j.val + 1 := fun hp => h ⟨by omega, by omega⟩
    simp [this]

private theorem sum_vrow (p q : ℕ) :
    ∑ j : Fin (n + nb), (vrow n p q j : ℝ) * Fin.append φ i j = potential φ p - potential φ q := by
  rw [Fin.sum_univ_add, Finset.sum_eq_zero (s := Finset.univ) (f := fun j : Fin nb =>
    (vrow n p q (Fin.natAdd n j) : ℝ) * Fin.append φ i (Fin.natAdd n j)), add_zero,
    ← sum_indicator_eq_potential φ p, ← sum_indicator_eq_potential φ q, ← Finset.sum_sub_distrib]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.append_left, vrow, Fin.val_castAdd, j.is_lt, ↓reduceIte, Rat.cast_sub,
      sub_mul]
  · intro j _
    simp [vrow]

private theorem sum_crow (b : Fin nb) :
    ∑ j : Fin (n + nb), (crow n b j : ℝ) * Fin.append φ i j = i b := by
  rw [Fin.sum_univ_add, Finset.sum_eq_zero, zero_add, Finset.sum_eq_single b]
  · simp [crow]
  · intro j _ hj
    have : ¬ (j.val = b.val) := fun h => hj (Fin.ext h)
    simp [crow, this]
  · simp
  · intro j _
    have : ¬ (j.val = n + b.val) := by omega
    simp [crow, this]

end Rows

namespace Netlist

variable {c : Netlist}

private theorem branch_eq (b : Fin c.branches.length) : c.branch b = c.branches.get b := by
  simp [branch, List.getD_eq_getElem?_getD]

private theorem E_apply (r j : Fin c.size) : c.mna.E r j = (c.eEntry r j : ℝ) :=
  realOfRows_rowsOf_apply _ r j

private theorem F_apply (r j : Fin c.size) : c.mna.F r j = (c.fEntry r j : ℝ) :=
  realOfRows_rowsOf_apply _ r j

private theorem G_apply (r : Fin c.size) (q : Fin c.inputs) :
    c.mna.G r q = (c.gEntry r q : ℝ) :=
  realOfRows_rowsOf_apply _ r q

private theorem b_apply (r : Fin c.size) : c.mna.b r = (c.bEntry r : ℝ) := by
  simp [mna, descriptorOfRows, bList, ofList_apply, List.getD_eq_getElem?_getD]

private theorem E_mulVec_castAdd (z : Fin c.size → ℝ) (k : Fin c.nodes) :
    (c.mna.E *ᵥ z) (Fin.castAdd _ k) = 0 := by
  simp [mulVec, dotProduct, E_apply, eEntry]

private theorem E_mulVec_natAdd (φ : Fin c.nodes → ℝ) (i : Fin c.branches.length → ℝ)
    (b : Fin c.branches.length) :
    (c.mna.E *ᵥ Fin.append φ i) (Fin.natAdd _ b) =
      ((c.branches.get b).elem.stamp.eV : ℝ) *
          (potential φ (c.branches.get b).pos - potential φ (c.branches.get b).neg) +
        ((c.branches.get b).elem.stamp.eI : ℝ) * i b := by
  simp only [mulVec, dotProduct, E_apply, eEntry, Fin.val_natAdd,
    show ¬ (c.nodes + b.val < c.nodes) by omega, ↓reduceIte, Nat.add_sub_cancel_left, branch_eq,
    Rat.cast_add, Rat.cast_mul, add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum, sum_vrow, sum_crow]

private theorem F_mulVec_castAdd (φ : Fin c.nodes → ℝ) (i : Fin c.branches.length → ℝ)
    (k : Fin c.nodes) :
    (c.mna.F *ᵥ Fin.append φ i) (Fin.castAdd _ k) =
      -∑ b, ((c.branches.get b).incidence (k + 1) : ℝ) * i b := by
  simp only [mulVec, dotProduct, F_apply]
  rw [Fin.sum_univ_add, Finset.sum_eq_zero, zero_add, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [fEntry, branch_eq]
  · intro j _
    have : ¬ c.nodes ≤ j.val := by omega
    simp [fEntry, this]

private theorem F_mulVec_natAdd (φ : Fin c.nodes → ℝ) (i : Fin c.branches.length → ℝ)
    (b : Fin c.branches.length) :
    (c.mna.F *ᵥ Fin.append φ i) (Fin.natAdd _ b) =
      ((c.branches.get b).elem.stamp.fV : ℝ) *
          (potential φ (c.branches.get b).pos - potential φ (c.branches.get b).neg) +
        ((c.branches.get b).elem.stamp.fI : ℝ) * i b +
        ((c.branches.get b).elem.stamp.fC : ℝ) *
          (potential φ (c.branches.get b).elem.stamp.cp -
            potential φ (c.branches.get b).elem.stamp.cn) := by
  simp only [mulVec, dotProduct, F_apply, fEntry, Fin.val_natAdd,
    show ¬ (c.nodes + b.val < c.nodes) by omega, ↓reduceIte, Nat.add_sub_cancel_left, branch_eq,
    Rat.cast_add, Rat.cast_mul, add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum, sum_vrow, sum_crow]

private theorem G_mulVec_castAdd (w : Fin c.inputs → ℝ) (k : Fin c.nodes) :
    (c.mna.G *ᵥ w) (Fin.castAdd _ k) = 0 := by
  simp [mulVec, dotProduct, G_apply, gEntry]

private theorem G_mulVec_natAdd (w : Fin c.inputs → ℝ) (b : Fin c.branches.length) :
    (c.mna.G *ᵥ w) (Fin.natAdd _ b) = inputValue w (c.branches.get b).elem.stamp.input := by
  simp only [mulVec, dotProduct, G_apply, gEntry, Fin.val_natAdd,
    show ¬ (c.nodes + b.val < c.nodes) by omega, ↓reduceIte, Nat.add_sub_cancel_left, branch_eq]
  cases (c.branches.get b).elem.stamp.input with
  | none => simp [inputValue]
  | some q =>
    simp only [Option.some.injEq, inputValue]
    split_ifs with hq
    · rw [Finset.sum_eq_single ⟨q, hq⟩]
      · simp
      · intro j _ hj
        have : q ≠ j.val := fun h => hj (Fin.ext h.symm)
        simp [this]
      · simp
    · refine Finset.sum_eq_zero fun j _ => ?_
      have : q ≠ j.val := fun h => hq (h ▸ j.is_lt)
      simp [this]

private theorem b_castAdd (k : Fin c.nodes) : c.mna.b (Fin.castAdd _ k) = 0 := by
  simp [b_apply, bEntry]

private theorem b_natAdd (b : Fin c.branches.length) :
    c.mna.b (Fin.natAdd _ b) = ((c.branches.get b).elem.stamp.src : ℝ) := by
  simp [b_apply, bEntry, branch_eq]

end Netlist

/-! ### Element laws as stamped equations -/

private theorem hasDerivWithinAt_zero_iff {s : Set ℝ} {t y : ℝ} (hs : UniqueDiffWithinAt ℝ s t) :
    HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) y s t ↔ y = 0 :=
  ⟨fun h => hs.eq_deriv _ h (hasDerivWithinAt_const t s 0), fun h => by
    rw [h]; exact hasDerivWithinAt_const t s 0⟩

private theorem hasDerivWithinAt_const_mul_iff {f : ℝ → ℝ} {s : Set ℝ} {t y a : ℝ} (ha : a ≠ 0) :
    HasDerivWithinAt (fun τ => a * f τ) y s t ↔ HasDerivWithinAt f (y / a) s t := by
  constructor
  · intro h
    have := h.const_mul a⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ ha, one_mul] at this
    simpa [div_eq_inv_mul] using this
  · intro h
    have := h.const_mul a
    rwa [mul_div_cancel₀ _ ha] at this

/-- The element law is the stamped equation of its row. -/
private theorem Element.law_iff {n m : ℕ} {e : Element} (he : e.check n m = true) {v i : ℝ → ℝ}
    {φ : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ} {s : Set ℝ} {t : ℝ} (hs : UniqueDiffWithinAt ℝ s t) :
    e.Law v i φ w s t ↔ HasDerivWithinAt (fun τ => (e.stamp.eV : ℝ) * v τ + (e.stamp.eI : ℝ) * i τ)
      ((e.stamp.fV : ℝ) * v t + (e.stamp.fI : ℝ) * i t +
        (e.stamp.fC : ℝ) * (potential (φ t) e.stamp.cp - potential (φ t) e.stamp.cn) +
        inputValue (w t) e.stamp.input + (e.stamp.src : ℝ)) s t := by
  cases e with
  | resistor R =>
    simp only [Element.Law, Element.stamp, Rat.cast_zero, zero_mul, add_zero, Rat.cast_one,
      one_mul, Rat.cast_neg, neg_mul, inputValue, hasDerivWithinAt_zero_iff hs]
    constructor <;> intro h <;> linarith
  | capacitor C =>
    have hC : (C : ℝ) ≠ 0 := by simp [Element.check] at he; exact_mod_cast he.ne'
    simp only [Element.Law, Element.stamp, Rat.cast_zero, zero_mul, add_zero, Rat.cast_one,
      one_mul, zero_add, inputValue, hasDerivWithinAt_const_mul_iff hC]
  | inductor L =>
    have hL : (L : ℝ) ≠ 0 := by simp [Element.check] at he; exact_mod_cast he.ne'
    simp only [Element.Law, Element.stamp, Rat.cast_zero, zero_mul, add_zero, Rat.cast_one,
      one_mul, zero_add, inputValue, hasDerivWithinAt_const_mul_iff hL]
  | voltageSource E input =>
    simp only [Element.Law, Element.stamp, Rat.cast_zero, zero_mul, add_zero, Rat.cast_neg,
      Rat.cast_one, neg_mul, one_mul, hasDerivWithinAt_zero_iff hs]
    constructor <;> intro h <;> linarith
  | currentSource J input =>
    simp only [Element.Law, Element.stamp, Rat.cast_zero, zero_mul, add_zero, zero_add,
      Rat.cast_neg, Rat.cast_one, neg_mul, one_mul, hasDerivWithinAt_zero_iff hs]
    constructor <;> intro h <;> linarith
  | vccs g cp cn =>
    simp only [Element.Law, Element.stamp, Rat.cast_zero, zero_mul, add_zero, zero_add,
      Rat.cast_neg, Rat.cast_one, neg_mul, one_mul, inputValue, hasDerivWithinAt_zero_iff hs]
    constructor <;> intro h <;> linarith
  | vcvs μ cp cn =>
    simp only [Element.Law, Element.stamp, Rat.cast_zero, zero_mul, add_zero,
      Rat.cast_neg, Rat.cast_one, neg_mul, one_mul, inputValue, hasDerivWithinAt_zero_iff hs]
    constructor <;> intro h <;> linarith

namespace Netlist

variable {c : Netlist}

/-- **Circuit trajectories are the solutions of the modified nodal equations.** For a
well-formed netlist and a time set with unique derivatives (such as `[0, ∞)`), potentials `φ` and
branch currents `i` form a Kirchhoff trajectory with input `u` exactly when `z = (φ, i)` solves
`E ż = F z + G u + b`. -/
theorem isTrajectoryOn_iff (hc : c.check = true) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {u : ℝ → Fin c.inputs → ℝ} {φ : ℝ → Fin c.nodes → ℝ} {i : ℝ → Fin c.branches.length → ℝ} :
    c.IsTrajectoryOn u φ i s ↔ c.mna.IsSolutionOn u (fun t => Fin.append (φ t) (i t)) s := by
  have hrow : ∀ t ∈ s, (HasDerivWithinAt (fun τ => c.mna.E *ᵥ Fin.append (φ τ) (i τ))
      (c.mna.F *ᵥ Fin.append (φ t) (i t) + c.mna.G *ᵥ u t + c.mna.b) s t ↔
      (∀ k : Fin c.nodes, ∑ b, ((c.branches.get b).incidence (k + 1) : ℝ) * i t b = 0) ∧
      ∀ b, (c.branches.get b).elem.Law
        (fun τ => potential (φ τ) (c.branches.get b).pos -
          potential (φ τ) (c.branches.get b).neg) (fun τ => i τ b) φ u s t) := by
    intro t ht
    rw [hasDerivWithinAt_pi, Fin.forall_fin_add]
    refine and_congr (forall_congr' fun k => ?_) (forall_congr' fun b => ?_)
    · simp only [Pi.add_apply, E_mulVec_castAdd, F_mulVec_castAdd, G_mulVec_castAdd, b_castAdd,
        add_zero, hasDerivWithinAt_zero_iff (hs t ht), neg_eq_zero]
    · have hb : (c.branches.get b).elem.check c.nodes c.inputs = true := by
        simp only [check, List.all_eq_true, Bool.and_eq_true] at hc
        exact (hc _ (List.get_mem _ _)).2
      rw [Element.law_iff hb (hs t ht)]
      simp only [Pi.add_apply, E_mulVec_natAdd, F_mulVec_natAdd, G_mulVec_natAdd, b_natAdd]
  constructor
  · intro h t ht
    exact (hrow t ht).2 ⟨h.kcl t ht, h.law t ht⟩
  · intro h
    exact ⟨fun t ht => ((hrow t ht).1 (h t ht)).1, fun t ht => ((hrow t ht).1 (h t ht)).2⟩

/-- The probe rows compute the probed quantities. -/
theorem probeRows_mulVec (probes : List Probe) (φ : Fin c.nodes → ℝ)
    (i : Fin c.branches.length → ℝ) :
    realOfRows probes.length c.size (c.probeRows probes) *ᵥ Fin.append φ i =
      fun o => (probes.get o).eval φ i := by
  funext o
  simp only [probeRows, mulVec, dotProduct, realOfRows_rowsOf_apply,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem o.is_lt, Option.getD_some,
    List.get_eq_getElem]
  cases probes[o.val] with
  | voltage p q => simp only [Probe.entry, Probe.eval, sum_vrow]
  | current b =>
    simp only [Probe.entry, Probe.eval]
    split_ifs with hb
    · exact sum_crow φ i ⟨b, hb⟩
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [Fin.append, Fin.addCases]
      have hj := j.is_lt
      have : ¬ (j.val = c.nodes + b) := by simp only [size] at hj; omega
      simp [crow, this]

/-- A vector of unknowns as a pair of potentials and branch currents. -/
private theorem append_split (z : Fin c.size → ℝ) :
    Fin.append (fun j => z (Fin.castAdd _ j)) (fun b => z (Fin.natAdd _ b)) = z :=
  Fin.append_castAdd_natAdd

/-- **Certified exponential stability of a circuit.** Let the netlist be well formed, let `d`
be an accepted index-one decoupling of its modified nodal equations, `z₀` an exactly checked
equilibrium (`F z₀ + b = 0`), and let `ẋ = A x` be exponentially stable for the checked reduced
matrix `d.A`, for instance by an accepted Lyapunov certificate
(`Cslib.LinearAlgebra.LyapunovCert.isExponentiallyStable_of_check`). Then, with zero input,

1. the operating point `z₀ = (φ₀, i₀)` is a (constant) circuit trajectory;
2. every differential state `x₀`, read through `Q₁'`, starts a circuit trajectory on `[0, ∞)`;
3. every circuit trajectory on `[0, ∞)` converges to `z₀` exponentially: for constants `M` and
   `α > 0` independent of the trajectory, `‖(φ t, i t) - z₀‖ ≤ M exp (-α t) ‖(φ 0, i 0) - z₀‖`
   in the Euclidean norm of all potentials and branch currents. -/
theorem isExponentiallyStable_of_check {d : DecouplingCert} {z₀ : List ℚ}
    (hc : c.check = true) (hd : d.check c.size c.eRows c.fRows = true)
    (hz : isEquilibriumRows c.size c.fRows c.bList z₀ = true)
    (hA : (toEuclideanCLM (𝕜 := ℝ) (realOfRows d.k d.k d.A)).IsExponentiallyStable) :
    c.IsTrajectoryOn 0 (fun _ j => realOfList c.size z₀ (Fin.castAdd _ j))
        (fun _ b => realOfList c.size z₀ (Fin.natAdd _ b)) (Ici 0) ∧
      (∀ x₀ : Fin d.k → ℝ, ∃ φ i, c.IsTrajectoryOn 0 φ i (Ici 0) ∧
        realOfRows d.k c.size d.Q₁' *ᵥ Fin.append (φ 0) (i 0) = x₀) ∧
      ∃ M α : ℝ, 0 < α ∧ ∀ φ i, c.IsTrajectoryOn 0 φ i (Ici 0) → ∀ t ≥ 0,
        ‖WithLp.toLp 2 (Fin.append (φ t) (i t) - realOfList c.size z₀)‖ ≤
          M * Real.exp (-(α * t)) *
            ‖WithLp.toLp 2 (Fin.append (φ 0) (i 0) - realOfList c.size z₀)‖ := by
  have hs := uniqueDiffOn_Ici (0 : ℝ)
  have heq : c.mna.IsEquilibrium (realOfList c.size z₀) := isEquilibrium_of_isEquilibriumRows hz
  set D := DecouplingCert.toDecoupling (m := c.inputs) (G := c.gRows) (b := c.bList) hd
  refine ⟨?_, fun x₀ => ?_, ?_⟩
  · rw [isTrajectoryOn_iff hc hs]
    simpa only [append_split] using heq.isSolutionOn (Ici 0)
  · obtain ⟨z, hz, h0⟩ := (D.exists_isSolutionOn_Ici_iff (u := 0) continuousOn_const
      (D.reconstruct x₀ 0)).2
      (by rw [DescriptorSystem.IndexOneDecoupling.Q₁'_mulVec_reconstruct]; rfl)
    refine ⟨fun t j => z t (Fin.castAdd _ j), fun t b => z t (Fin.natAdd _ b), ?_, ?_⟩
    · have hz' : c.mna.IsSolutionOn 0 z (Ici 0) := hz
      rw [isTrajectoryOn_iff hc hs]
      convert hz' using 1
      funext t
      exact append_split (z t)
    · rw [append_split, h0]
      exact DescriptorSystem.IndexOneDecoupling.Q₁'_mulVec_reconstruct (D := D) x₀ 0
  · obtain ⟨M, α, hα, hM⟩ := DecouplingCert.isExponentiallyStableAt_of_check
      (m := c.inputs) (G := c.gRows) hd hz hA
    exact ⟨M, α, hα, fun φ i h t ht => hM _ ((isTrajectoryOn_iff hc hs).1 h) t ht⟩

/-- The checked realization of a circuit for the probes `probes` and its input ports, with the
rational matrices computed from the decoupling `d` (`DecouplingCert.A`, `reducedB`,
`outputC` and `feedthroughD`). -/
@[expose] noncomputable def realization (d : DecouplingCert) (probes : List Probe) :
    LTISystem (Fin d.k) (Fin c.inputs) (Fin probes.length) where
  A := realOfRows d.k d.k d.A
  B := realOfRows d.k c.inputs (d.reducedB c.size c.inputs c.gRows)
  C := realOfRows probes.length d.k (d.outputC c.size probes.length (c.probeRows probes))
  D := realOfRows probes.length c.inputs
    (d.feedthroughD c.size probes.length c.inputs (c.probeRows probes) c.gRows)

/-- **Checked proper realization.** Let the netlist be well formed, `d` an accepted decoupling
and `z₀` a checked equilibrium. On a time set with unique derivatives (such as `[0, ∞)`) and for
every input signal `u`, `(φ, i)` is a circuit trajectory exactly when

1. the vector `z = (φ, i)` is reconstructed from the state `x = Q₁' (z - z₀)` and the input:
   `z = z₀ + Q₁ x - Q₂ P₂ G u`, and
2. `x` solves `ẋ = A x + B u` of `c.realization d probes`.

The probed outputs then satisfy `y - y₀ = C x + D u` (`IsTrajectoryOn.probe_sub_eq`). -/
theorem isTrajectoryOn_iff_realization {d : DecouplingCert} {z₀ : List ℚ} (hc : c.check = true)
    (hd : d.check c.size c.eRows c.fRows = true)
    (hz : isEquilibriumRows c.size c.fRows c.bList z₀ = true) (probes : List Probe)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {u : ℝ → Fin c.inputs → ℝ} {φ : ℝ → Fin c.nodes → ℝ}
    {i : ℝ → Fin c.branches.length → ℝ} :
    c.IsTrajectoryOn u φ i s ↔
      (∀ t ∈ s, Fin.append (φ t) (i t) = realOfList c.size z₀ +
          realOfRows c.size d.k d.Q₁ *ᵥ (realOfRows d.k c.size d.Q₁' *ᵥ
            (Fin.append (φ t) (i t) - realOfList c.size z₀)) -
          realOfRows c.size d.r d.Q₂ *ᵥ (realOfRows d.r c.size d.P₂ *ᵥ
            (realOfRows c.size c.inputs c.gRows *ᵥ u t))) ∧
      (c.realization d probes).IsSolutionOn u
        (fun t => realOfRows d.k c.size d.Q₁' *ᵥ (Fin.append (φ t) (i t) - realOfList c.size z₀))
        s := by
  rw [isTrajectoryOn_iff hc hs]
  refine ((DecouplingCert.toDecoupling (m := c.inputs) (G := c.gRows) (b := c.bList)
    hd).isSolutionOn_iff_realization (realOfRows probes.length c.size (c.probeRows probes))
      (isEquilibrium_of_isEquilibriumRows hz) hs).trans ?_
  rw [DecouplingCert.realization_toDecoupling]
  rfl

/-- **Output equation.** Along a circuit trajectory, the probed outputs differ from their values
at the operating point by `C x + D u`, where `x = Q₁' (z - z₀)` is the realization's state. -/
theorem IsTrajectoryOn.probe_sub_eq {d : DecouplingCert} {z₀ : List ℚ} (hc : c.check = true)
    (hd : d.check c.size c.eRows c.fRows = true)
    (hz : isEquilibriumRows c.size c.fRows c.bList z₀ = true) (probes : List Probe)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {u : ℝ → Fin c.inputs → ℝ} {φ : ℝ → Fin c.nodes → ℝ}
    {i : ℝ → Fin c.branches.length → ℝ} (h : c.IsTrajectoryOn u φ i s) {t : ℝ} (ht : t ∈ s) :
    (fun o => (probes.get o).eval (φ t) (i t)) -
        (fun o => (probes.get o).eval (fun j => realOfList c.size z₀ (Fin.castAdd _ j))
          (fun b => realOfList c.size z₀ (Fin.natAdd _ b))) =
      (c.realization d probes).C *ᵥ
          (realOfRows d.k c.size d.Q₁' *ᵥ (Fin.append (φ t) (i t) - realOfList c.size z₀)) +
        (c.realization d probes).D *ᵥ u t := by
  have hrec := ((isTrajectoryOn_iff_realization hc hd hz probes hs).1 h).1 t ht
  have := (DecouplingCert.toDecoupling (m := c.inputs) (G := c.gRows) (b := c.bList) hd).output_eq
    (realOfRows probes.length c.size (c.probeRows probes)) hrec
  rw [DecouplingCert.realization_toDecoupling] at this
  rw [← probeRows_mulVec, ← probeRows_mulVec, append_split]
  exact this

end Netlist

end Cslib.Electrical
