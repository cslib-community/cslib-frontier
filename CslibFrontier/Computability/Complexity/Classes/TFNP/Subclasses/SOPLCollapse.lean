/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLineCollapse
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.BinaryWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Tactic.PolyTime

/-!
# `SOPL = PLS ∩ PPADS` and `EOPL = PLS ∩ PPAD`

We prove `PLS ∩ PPADS ⊆ SOPL` [Göös et al., Section 4, Lemma 3][GoosEtAl2022] using the
path-pigeonhole gadget of [Göös et al., Section 3, Lemma 2][GoosEtAl2022], and deduce the two main
collapses of [Göös et al.][GoosEtAl2022]:

* **Theorem 2** (`Cslib.Complexity.SOPL_eq_PLS_inter_PPADS`): `SOPL = PLS ∩ PPADS`, combining
  `PLS_inter_PPADS_subset_SOPL` with `SOPL_subset_PLS_inter_PPADS`.
* **Theorem 1** (`Cslib.Complexity.EOPL_eq_PLS_inter_PPAD`): `EOPL = PLS ∩ PPAD`, combining
  `SOPL = PLS ∩ PPADS`, `PPAD ⊆ PPADS`, and `EOPL = SOPL ∩ PPAD`
  (`Cslib.Complexity.EOPL_eq_SOPL_inter_PPAD`).

## The construction

Fix an instance `a`. Let `(n₁, N₁, C₁)` be a local-search family (`PLS`) whose costs on
`{0, 1} ^ (n₁ a)` lie strictly below `B a`, and let `(n₂, P₂, S₂)` be a sink-of-line family
(`PPADS`). Put `m := n₁ a + n₂ a`, `T := 2 ^ m`, `K := 2 ^ (n₂ a)`, and
`M := T - K = (2 ^ (n₁ a) - 1) * K`.

The combined sink-of-potential-line instance lives on strings `x ++ (z ++ r)` of width
`plsPpadsWidth n₁ n₂ a = n₁ a + m + m`, with `x ∈ {0, 1} ^ (n₁ a)` and `z, r ∈ {0, 1} ^ m`
encoding binary indices `α := binaryValue z < T` and `k := binaryValue r < T`:

1. **Sink-of-line to injective pigeonhole** ([Göös et al., Lemma 1][GoosEtAl2022]): on
   `{0, 1} ^ (n₂ a)`, mapping `y` to `S₂ (a, y)` along active outgoing edges and fixing isolated
   vertices `y ≠ 0 ^ (n₂ a)` defines a reversible partial injection from `{0, …, K - 1}`
   (`y = binaryWord (n₂ a) α`) into the `K - 1` holes `{0, …, K - 2}` (`binaryValue y' - 1` for
   `y' ≠ 0 ^ (n₂ a)`), whose missing pigeons are precisely the solutions of
   `sinkOfLineRel n₂ P₂ S₂ a`.
2. **Path-pigeonhole gadget** ([Göös et al., Lemma 2][GoosEtAl2022]): for each non-optimal `PLS`
   vertex `x` (`C₁ (a, N₁ (a, x)) < C₁ (a, x)`), columns `k = 0, …, M` route `T` incoming copies
   down to `K` outgoing copies one pigeonhole compression at a time: at step `k < M`, copies
   `0 ≤ α < K` apply the partial injection into `{0, …, K - 2}`, while copies `K ≤ α < T - k` shift
   to `α - 1 ∈ {K - 1, …, T - (k + 1) - 1}`. Local optima `x` (`C₁ (a, x) ≤ C₁ (a, N₁ (a, x))`)
   have no gadget edges.
3. **Reversible `PLS` transitions** ([Göös et al., Lemma 3][GoosEtAl2022]): at column `k = M`, the
   surviving `K` copies `α < K` (`i = binaryWord (n₂ a) α`) of a non-optimal `x` step to
   `(N₁ (a, x), x ++ i, 0 ^ m)`, recording the predecessor `x` in the upper `n₁ a` bits of `z'` so
   predecessors at `k' = 0` are computed in polynomial time without merging paths.

With potential `V (x, z, r) = (B a - C₁ (a, x)) * T + binaryValue r`, intra-gadget steps increase
`V` by `1` and inter-gadget steps increase `B a - C₁ (a, x)` by at least `1` while dropping
`binaryValue r` by `M < T`, so `V` strictly increases along every edge and no edge is pruned
(`hasPotentialOut_plsPpads`, `hasPotentialIn_plsPpads`). Every sink of the combined instance decodes
either directly to a `PLS` local optimum at `x` or to a `PPADS` sink at
`binaryWord (n₂ a) (binaryValue z)` (`plsPpads_sink`).

## Main definitions

* `Cslib.Complexity.plsPpadsWidth`: vertex bit-length `n₁ a + (n₁ a + n₂ a) + (n₁ a + n₂ a)`.
* `Cslib.Complexity.plsPpadsSucc`, `Cslib.Complexity.plsPpadsPred`,
  `Cslib.Complexity.plsPpadsPotential`: the combined sink-of-potential-line instance.

## Main results

* `Cslib.Complexity.plsPpads_sink`: sinks of the combined instance decode to `PLS` or `PPADS`
  solutions.
* `Cslib.Complexity.mem_SOPL_of_localOpt_sinkOfLine`: a problem in `FNP` that reduces on the same
  instance to both a `PLS` family and a `PPADS` family lies in `SOPL`.
* `Cslib.Complexity.PLS_inter_PPADS_subset_SOPL`, `Cslib.Complexity.SOPL_eq_PLS_inter_PPADS`.
* `Cslib.Complexity.PLS_inter_PPAD_subset_EOPL`, `Cslib.Complexity.EOPL_eq_PLS_inter_PPAD`.

## References

* [M. Göös, A. Hollender, S. Jain, G. Maystre, W. Pires, R. Robere, R. Tao, *Further Collapses in
  TFNP*][GoosEtAl2022]
-/

public section

namespace Cslib.Complexity

open Cslib.BitString Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type}

/-! ### Binary-word helpers -/

private theorem binaryWord_binaryValue {w : ℕ} {u : List Bool} (hu : u.length = w) :
    binaryWord w (binaryValue u) = u :=
  binaryValue_injective_of_length_eq
    ((length_binaryWord (hu ▸ binaryValue_lt_two_pow u)).trans hu.symm)
    (binaryValue_binaryWord w (binaryValue u))

private theorem binaryValue_zeroVertex (w : ℕ) : binaryValue (zeroVertex w) = 0 := by
  simpa only [List.append_nil, zeroVertex, binaryValue, List.foldl_nil] using
    binaryValue_replicate_false_append w []

private theorem eq_zeroVertex_iff_binaryValue_eq_zero {w : ℕ} {u : List Bool}
    (hu : u.length = w) : u = zeroVertex w ↔ binaryValue u = 0 := by
  refine ⟨fun h => h ▸ binaryValue_zeroVertex w, fun h => ?_⟩
  exact binaryValue_injective_of_length_eq (hu.trans (length_zeroVertex w).symm)
    (h.trans (binaryValue_zeroVertex w).symm)

private theorem zeroVertex_three (k m : ℕ) :
    zeroVertex (k + m + m) = zeroVertex k ++ (zeroVertex m ++ zeroVertex m) := by
  simp only [zeroVertex, List.replicate_append_replicate, Nat.add_assoc]

private theorem append_three_eq_zeroVertex_iff {k m : ℕ} {x z r : List Bool}
    (hx : x.length = k) (hz : z.length = m) :
    x ++ (z ++ r) = zeroVertex (k + m + m) ↔
      x = zeroVertex k ∧ z = zeroVertex m ∧ r = zeroVertex m := by
  rw [zeroVertex_three]
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩
  obtain ⟨hx0, hzr⟩ := List.append_inj h (by simp [hx])
  exact ⟨hx0, List.append_inj hzr (by simp [hz])⟩

private theorem append_three_inj {k m : ℕ} {x₁ z₁ r₁ x₂ z₂ r₂ : List Bool}
    (hx₁ : x₁.length = k) (hz₁ : z₁.length = m)
    (hx₂ : x₂.length = k) (hz₂ : z₂.length = m)
    (h : x₁ ++ (z₁ ++ r₁) = x₂ ++ (z₂ ++ r₂)) :
    x₁ = x₂ ∧ z₁ = z₂ ∧ r₁ = r₂ := by
  obtain ⟨hx, hzr⟩ := List.append_inj h (hx₁.trans hx₂.symm)
  obtain ⟨hz, hr⟩ := List.append_inj hzr (hz₁.trans hz₂.symm)
  exact ⟨hx, hz, hr⟩

private theorem exists_append_three {k m : ℕ} {w : List Bool} (hw : w.length = k + m + m) :
    ∃ x z r, w = x ++ (z ++ r) ∧ x.length = k ∧ z.length = m ∧ r.length = m := by
  refine ⟨w.take k, (w.drop k).take m, (w.drop k).drop m, ?_, ?_, ?_, ?_⟩
  · simp [List.take_append_drop]
  · simp only [List.length_take]; omega
  · simp only [List.length_take, List.length_drop]; omega
  · simp only [List.length_drop]; omega

/-! ### The combined `SOPL` instance -/

/-- Vertex bit-length `n₁ a + (n₁ a + n₂ a) + (n₁ a + n₂ a)` of the combined `SOPL` instance for
`PLS ∩ PPADS ⊆ SOPL`. -/
abbrev plsPpadsWidth (n₁ n₂ : α → ℕ) (a : α) : ℕ :=
  n₁ a + (n₁ a + n₂ a) + (n₁ a + n₂ a)

/-- Successor map of the combined `SOPL` instance on `x ++ (z ++ r)` with `|x| = n₁ a` and
`|z| = |r| = n₁ a + n₂ a`. Non-optimal `PLS` vertices `x` (`C₁ (a, N₁ (a, x)) < C₁ (a, x)`) traverse
the `(2 ^ (n₁ a + n₂ a) - 2 ^ (n₂ a))`-column path-pigeonhole gadget built from `(n₂, P₂, S₂)` and
then step at column `M` from `(x, α, M)` (`α < 2 ^ (n₂ a)`) to
`(N₁ (a, x), x ++ binaryWord (n₂ a) α, 0)`. -/
@[expose] def plsPpadsSuccCore (n₁ : α → ℕ) (N₁ : α × List Bool → List Bool)
    (C₁ : α × List Bool → ℕ) (n₂ : α → ℕ) (P₂ S₂ : α × List Bool → List Bool)
    (a : α) (x z r : List Bool) : List Bool :=
  let m := n₁ a + n₂ a
  let T := 2 ^ m
  let K := 2 ^ n₂ a
  let M := T - K
  let α := binaryValue z
  let k := binaryValue r
  let y := binaryWord (n₂ a) α
  if decide (C₁ (a, N₁ (a, x)) < C₁ (a, x)) then
    if decide (k < M) then
      if decide (α < K) then
        if hasOut n₂ P₂ S₂ a y then
          x ++ (binaryWord m (binaryValue (S₂ (a, y)) - 1) ++ binaryWord m (k + 1))
        else if !decide (y = zeroVertex (n₂ a)) && !hasIn n₂ P₂ S₂ a y then
          x ++ (binaryWord m (α - 1) ++ binaryWord m (k + 1))
        else
          x ++ (z ++ r)
      else if decide (α < T - k) then
        x ++ (binaryWord m (α - 1) ++ binaryWord m (k + 1))
      else
        x ++ (z ++ r)
    else if decide (k = M) && decide (α < K) then
      N₁ (a, x) ++ ((x ++ y) ++ zeroVertex m)
    else
      x ++ (z ++ r)
  else
    x ++ (z ++ r)

/-- Predecessor map of the combined `SOPL` instance on `x' ++ (z' ++ r')`, inverse to
`plsPpadsSuccCore` on its active edges. -/
@[expose] def plsPpadsPredCore (n₁ : α → ℕ) (N₁ : α × List Bool → List Bool)
    (C₁ : α × List Bool → ℕ) (n₂ : α → ℕ) (P₂ S₂ : α × List Bool → List Bool)
    (a : α) (x' z' r' : List Bool) : List Bool :=
  let m := n₁ a + n₂ a
  let T := 2 ^ m
  let K := 2 ^ n₂ a
  let M := T - K
  let α' := binaryValue z'
  let k' := binaryValue r'
  let x₀ := z'.take (n₁ a)
  let i₀ := z'.drop (n₁ a)
  let y' := binaryWord (n₂ a) (α' + 1)
  if decide (k' = 0) then
    if decide (C₁ (a, N₁ (a, x₀)) < C₁ (a, x₀)) && decide (N₁ (a, x₀) = x') then
      x₀ ++ (binaryWord m (binaryValue i₀) ++ binaryWord m M)
    else
      x' ++ (z' ++ r')
  else if decide (k' ≤ M) && decide (C₁ (a, N₁ (a, x')) < C₁ (a, x')) then
    if decide (α' + 1 < K) then
      if hasIn n₂ P₂ S₂ a y' then
        x' ++ (binaryWord m (binaryValue (P₂ (a, y'))) ++ binaryWord m (k' - 1))
      else if !hasOut n₂ P₂ S₂ a y' then
        x' ++ (binaryWord m (α' + 1) ++ binaryWord m (k' - 1))
      else
        x' ++ (z' ++ r')
    else if decide (α' < T - k') then
      x' ++ (binaryWord m (α' + 1) ++ binaryWord m (k' - 1))
    else
      x' ++ (z' ++ r')
  else
    x' ++ (z' ++ r')

/-- Successor map of the combined `SOPL` instance on strings of length `plsPpadsWidth n₁ n₂ a`. -/
@[expose] def plsPpadsSucc (n₁ : α → ℕ) (N₁ : α × List Bool → List Bool)
    (C₁ : α × List Bool → ℕ) (n₂ : α → ℕ) (P₂ S₂ : α × List Bool → List Bool)
    (p : α × List Bool) : List Bool :=
  plsPpadsSuccCore n₁ N₁ C₁ n₂ P₂ S₂ p.1
    (p.2.take (n₁ p.1))
    ((p.2.drop (n₁ p.1)).take (n₁ p.1 + n₂ p.1))
    ((p.2.drop (n₁ p.1)).drop (n₁ p.1 + n₂ p.1))

/-- Predecessor map of the combined `SOPL` instance on strings of length `plsPpadsWidth n₁ n₂ a`. -/
@[expose] def plsPpadsPred (n₁ : α → ℕ) (N₁ : α × List Bool → List Bool)
    (C₁ : α × List Bool → ℕ) (n₂ : α → ℕ) (P₂ S₂ : α × List Bool → List Bool)
    (p : α × List Bool) : List Bool :=
  plsPpadsPredCore n₁ N₁ C₁ n₂ P₂ S₂ p.1
    (p.2.take (n₁ p.1))
    ((p.2.drop (n₁ p.1)).take (n₁ p.1 + n₂ p.1))
    ((p.2.drop (n₁ p.1)).drop (n₁ p.1 + n₂ p.1))

/-- Potential of the combined `SOPL` instance:
`(B a - C₁ (a, x)) * 2 ^ (n₁ a + n₂ a) + binaryValue r`, where `B a` strictly bounds `C₁ (a, ·)` on
`{0, 1} ^ (n₁ a)`. -/
@[expose] def plsPpadsPotential (n₁ : α → ℕ) (C₁ : α × List Bool → ℕ) (n₂ B : α → ℕ)
    (p : α × List Bool) : ℕ :=
  (B p.1 - C₁ (p.1, p.2.take (n₁ p.1))) * 2 ^ (n₁ p.1 + n₂ p.1) +
    binaryValue ((p.2.drop (n₁ p.1)).drop (n₁ p.1 + n₂ p.1))

variable {n₁ n₂ B : α → ℕ} {N₁ P₂ S₂ : α × List Bool → List Bool} {C₁ : α × List Bool → ℕ}
  {a : α} {x z r : List Bool}

theorem plsPpadsSucc_append (hx : x.length = n₁ a) (hz : z.length = n₁ a + n₂ a) :
    plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂ (a, x ++ (z ++ r)) =
      plsPpadsSuccCore n₁ N₁ C₁ n₂ P₂ S₂ a x z r := by
  simp [plsPpadsSucc, List.take_left' hx, List.drop_left' hx, List.take_left' hz,
    List.drop_left' hz]

theorem plsPpadsPred_append (hx : x.length = n₁ a) (hz : z.length = n₁ a + n₂ a) :
    plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂ (a, x ++ (z ++ r)) =
      plsPpadsPredCore n₁ N₁ C₁ n₂ P₂ S₂ a x z r := by
  simp [plsPpadsPred, List.take_left' hx, List.drop_left' hx, List.take_left' hz,
    List.drop_left' hz]

theorem plsPpadsPotential_append (hx : x.length = n₁ a) (hz : z.length = n₁ a + n₂ a) :
    plsPpadsPotential n₁ C₁ n₂ B (a, x ++ (z ++ r)) =
      (B a - C₁ (a, x)) * 2 ^ (n₁ a + n₂ a) + binaryValue r := by
  simp [plsPpadsPotential, List.take_left' hx, List.drop_left' hx, List.drop_left' hz]

/-! ### Edges of the combined instance -/

private theorem two_pow_le_two_pow_add (k m : ℕ) : 2 ^ m ≤ 2 ^ (k + m) :=
  Nat.pow_le_pow_right (by decide) (Nat.le_add_left m k)

private theorem two_pow_sub_lt (k m : ℕ) : 2 ^ (k + m) - 2 ^ m < 2 ^ (k + m) :=
  Nat.sub_lt (Nat.two_pow_pos _) (Nat.two_pow_pos m)

private theorem binaryValue_lt_of_length {w : List Bool} {n : ℕ} (h : w.length = n) :
    binaryValue w < 2 ^ n :=
  h ▸ binaryValue_lt_two_pow w

private theorem length_ite_bool {b : Bool} {l₁ l₂ : List Bool} {n : ℕ}
    (h₁ : b = true → l₁.length = n) (h₂ : b = false → l₂.length = n) :
    (if b then l₁ else l₂).length = n := by
  cases b <;> [exact h₂ rfl; exact h₁ rfl]

private theorem plsPpadsPotential_jump_lt {k m B c₁ c₂ : ℕ}
    (hstep : c₁ < c₂) (hB : c₂ < B) :
    (B - c₂) * 2 ^ (k + m) + (2 ^ (k + m) - 2 ^ m) < (B - c₁) * 2 ^ (k + m) := by
  have hle := Nat.mul_le_mul_right (2 ^ (k + m)) (show B - c₂ + 1 ≤ B - c₁ by omega)
  rw [Nat.add_mul, Nat.one_mul] at hle
  have := two_pow_sub_lt k m
  omega

/-- Every moved vertex under `plsPpadsSucc` has a consistent predecessor, avoids `0 ^ W`, and
strictly increases `plsPpadsPotential`. -/
private theorem plsPpadsSucc_spec (hx : x.length = n₁ a) (hz : z.length = n₁ a + n₂ a)
    (hr : r.length = n₁ a + n₂ a)
    (hN₁ : ∀ u, u.length = n₁ a → (N₁ (a, u)).length = n₁ a)
    (hS₂ : ∀ u, u.length = n₂ a → (S₂ (a, u)).length = n₂ a)
    (hB : ∀ u, u.length = n₁ a → C₁ (a, u) < B a)
    (h : plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂ (a, x ++ (z ++ r)) ≠ x ++ (z ++ r)) :
    plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂
        (a, plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂ (a, x ++ (z ++ r))) = x ++ (z ++ r) ∧
      plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂ (a, x ++ (z ++ r)) ≠
        zeroVertex (plsPpadsWidth n₁ n₂ a) ∧
      plsPpadsPotential n₁ C₁ n₂ B (a, x ++ (z ++ r)) <
        plsPpadsPotential n₁ C₁ n₂ B
          (a, plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂ (a, x ++ (z ++ r))) := by
  have hBx := hB x hx
  have hαT := binaryValue_lt_of_length hz
  have hkT := binaryValue_lt_of_length hr
  have hKT := two_pow_le_two_pow_add (n₁ a) (n₂ a)
  have hKpos := Nat.two_pow_pos (n₂ a)
  rw [plsPpadsSucc_append hx hz] at h ⊢
  rw [plsPpadsPotential_append hx hz]
  dsimp only [plsPpadsSuccCore] at h ⊢
  by_cases hstep : C₁ (a, N₁ (a, x)) < C₁ (a, x)
  · simp only [decide_eq_true hstep, ↓reduceIte] at h ⊢
    by_cases hkM : binaryValue r < 2 ^ (n₁ a + n₂ a) - 2 ^ n₂ a
    · simp only [decide_eq_true hkM, ↓reduceIte] at h ⊢
      have hk1T : binaryValue r + 1 < 2 ^ (n₁ a + n₂ a) := by omega
      have hk1M : binaryValue r + 1 ≤ 2 ^ (n₁ a + n₂ a) - 2 ^ n₂ a := by omega
      have hk1_ne : binaryValue r + 1 ≠ 0 := by omega
      have gadget_tail {v : ℕ} (hv : v < 2 ^ (n₁ a + n₂ a)) :
          x ++ (binaryWord (n₁ a + n₂ a) v ++
              binaryWord (n₁ a + n₂ a) (binaryValue r + 1)) ≠
            zeroVertex (plsPpadsWidth n₁ n₂ a) ∧
          (B a - C₁ (a, x)) * 2 ^ (n₁ a + n₂ a) + binaryValue r <
            plsPpadsPotential n₁ C₁ n₂ B (a, x ++ (binaryWord (n₁ a + n₂ a) v ++
              binaryWord (n₁ a + n₂ a) (binaryValue r + 1))) := by
        have hz' := length_binaryWord hv
        refine ⟨fun h0 => hk1_ne ?_, ?_⟩
        · simpa only [binaryValue_binaryWord, binaryValue_zeroVertex] using
            congrArg binaryValue ((append_three_eq_zeroVertex_iff hx hz').mp h0).2.2
        · rw [plsPpadsPotential_append hx hz', binaryValue_binaryWord]
          omega
      by_cases hαK : binaryValue z < 2 ^ n₂ a
      · simp only [decide_eq_true hαK, ↓reduceIte] at h ⊢
        have hy_len : (binaryWord (n₂ a) (binaryValue z)).length = n₂ a := length_binaryWord hαK
        cases hout : hasOut n₂ P₂ S₂ a (binaryWord (n₂ a) (binaryValue z))
        · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hc : (!decide (binaryWord (n₂ a) (binaryValue z) = zeroVertex (n₂ a)) &&
              !hasIn n₂ P₂ S₂ a (binaryWord (n₂ a) (binaryValue z)))
          · simp only [hout, hc, Bool.false_eq_true, ↓reduceIte] at h
            exact absurd rfl h
          · simp only [↓reduceIte]
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
            have hα_pos : 0 < binaryValue z := by
              have hne := mt (eq_zeroVertex_iff_binaryValue_eq_zero hy_len).mpr hc.1
              rw [binaryValue_binaryWord] at hne; omega
            refine ⟨?_, gadget_tail (by omega)⟩
            rw [plsPpadsPred_append hx (length_binaryWord (by omega))]
            dsimp only [plsPpadsPredCore]
            simp only [binaryValue_binaryWord, decide_eq_false hk1_ne, Bool.false_eq_true,
              ↓reduceIte, decide_eq_true hk1M, decide_eq_true hstep, Bool.and_self,
              show binaryValue z - 1 + 1 = binaryValue z by omega, decide_eq_true hαK, hc.2,
              hout, Bool.not_false, Nat.add_sub_cancel, binaryWord_binaryValue hz,
              binaryWord_binaryValue hr]
        · simp only [↓reduceIte]
          have hout' := hout
          simp only [hasOut, decide_eq_true_eq] at hout'
          have hS_len := hS₂ _ hy_len
          have hS_lt := binaryValue_lt_of_length hS_len
          have hS_pos : 0 < binaryValue (S₂ (a, binaryWord (n₂ a) (binaryValue z))) := by
            have hne := mt (eq_zeroVertex_iff_binaryValue_eq_zero hS_len).mpr hout'.2.2; omega
          refine ⟨?_, gadget_tail (by omega)⟩
          rw [plsPpadsPred_append hx (length_binaryWord (by omega))]
          dsimp only [plsPpadsPredCore]
          simp only [binaryValue_binaryWord, decide_eq_false hk1_ne, Bool.false_eq_true,
            ↓reduceIte, decide_eq_true hk1M, decide_eq_true hstep, Bool.and_self,
            show binaryValue (S₂ (a, binaryWord (n₂ a) (binaryValue z))) - 1 + 1 =
              binaryValue (S₂ (a, binaryWord (n₂ a) (binaryValue z))) by omega,
            decide_eq_true hS_lt, binaryWord_binaryValue hS_len, hasIn_of_hasOut hout, hout'.1,
            Nat.add_sub_cancel, binaryWord_binaryValue hz, binaryWord_binaryValue hr]
      · simp only [decide_eq_false hαK, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hαTk : binaryValue z < 2 ^ (n₁ a + n₂ a) - binaryValue r
        · simp only [decide_eq_true hαTk, ↓reduceIte]
          have hα'_lt : binaryValue z - 1 < 2 ^ (n₁ a + n₂ a) - (binaryValue r + 1) := by omega
          refine ⟨?_, gadget_tail (by omega)⟩
          rw [plsPpadsPred_append hx (length_binaryWord (by omega))]
          dsimp only [plsPpadsPredCore]
          simp only [binaryValue_binaryWord, decide_eq_false hk1_ne, Bool.false_eq_true,
            ↓reduceIte, decide_eq_true hk1M, decide_eq_true hstep, Bool.and_self,
            show binaryValue z - 1 + 1 = binaryValue z by omega, decide_eq_false hαK,
            decide_eq_true hα'_lt, Nat.add_sub_cancel, binaryWord_binaryValue hz,
            binaryWord_binaryValue hr]
        · simp [decide_eq_false hαTk] at h
    · simp only [decide_eq_false hkM, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hc : (decide (binaryValue r = 2 ^ (n₁ a + n₂ a) - 2 ^ n₂ a) &&
          decide (binaryValue z < 2 ^ n₂ a))
      · simp [hc] at h
      · simp only [↓reduceIte]
        obtain ⟨hk_eq, hαK⟩ := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using hc
        have hNx_len : (N₁ (a, x)).length = n₁ a := hN₁ x hx
        have hxy_len : (x ++ binaryWord (n₂ a) (binaryValue z)).length = n₁ a + n₂ a := by
          simp [hx, length_binaryWord hαK]
        refine ⟨?_, ?_, ?_⟩
        · rw [plsPpadsPred_append hNx_len hxy_len]
          dsimp only [plsPpadsPredCore]
          simp only [binaryValue_zeroVertex, decide_true, ↓reduceIte,
            List.take_left' hx, List.drop_left' hx, decide_eq_true hstep, Bool.and_self,
            binaryValue_binaryWord, binaryWord_binaryValue hz, ← hk_eq,
            binaryWord_binaryValue hr]
        · rw [ne_eq, append_three_eq_zeroVertex_iff hNx_len hxy_len]
          rintro ⟨hN0, hxy0, -⟩
          have hx0 : x = zeroVertex (n₁ a) := by
            simpa [List.take_left' hx, zeroVertex, List.replicate_append_replicate] using
              congrArg (List.take (n₁ a)) hxy0
          rw [hN0, hx0] at hstep; exact Nat.lt_irrefl _ hstep
        · rw [plsPpadsPotential_append hNx_len hxy_len, binaryValue_zeroVertex, hk_eq, add_zero]
          exact plsPpadsPotential_jump_lt hstep hBx
  · simp [decide_eq_false hstep] at h

/-- Every moved vertex under `plsPpadsPred` points forward under `plsPpadsSucc` and has strictly
smaller `plsPpadsPotential`. -/
private theorem plsPpadsPred_spec (hx : x.length = n₁ a) (hz : z.length = n₁ a + n₂ a)
    (hr : r.length = n₁ a + n₂ a)
    (hP₂ : ∀ u, u.length = n₂ a → (P₂ (a, u)).length = n₂ a)
    (hB : ∀ u, u.length = n₁ a → C₁ (a, u) < B a)
    (h : plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂ (a, x ++ (z ++ r)) ≠ x ++ (z ++ r)) :
    plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂
        (a, plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂ (a, x ++ (z ++ r))) = x ++ (z ++ r) ∧
      plsPpadsPotential n₁ C₁ n₂ B
          (a, plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂ (a, x ++ (z ++ r))) <
        plsPpadsPotential n₁ C₁ n₂ B (a, x ++ (z ++ r)) := by
  have hkT := binaryValue_lt_of_length hr
  have hKT := two_pow_le_two_pow_add (n₁ a) (n₂ a)
  have hMT := two_pow_sub_lt (n₁ a) (n₂ a)
  rw [plsPpadsPred_append hx hz] at h ⊢
  rw [plsPpadsPotential_append hx hz]
  dsimp only [plsPpadsPredCore] at h ⊢
  by_cases hk0 : binaryValue r = 0
  · simp only [decide_eq_true hk0, ↓reduceIte] at h ⊢
    cases hc : (decide (C₁ (a, N₁ (a, z.take (n₁ a))) < C₁ (a, z.take (n₁ a))) &&
        decide (N₁ (a, z.take (n₁ a)) = x))
    · simp [hc] at h
    · simp only [↓reduceIte]
      obtain ⟨hstep₀, hNx₀⟩ := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using hc
      have hx₀_len : (z.take (n₁ a)).length = n₁ a := by simp only [List.length_take, hz]; omega
      have hi₀_len : (z.drop (n₁ a)).length = n₂ a := by simp only [List.length_drop, hz]; omega
      have hi₀_lt := binaryValue_lt_of_length hi₀_len
      have hz₀_len := length_binaryWord (w := n₁ a + n₂ a) (hi₀_lt.trans_le hKT)
      have hBx₀ := hB _ hx₀_len
      refine ⟨?_, ?_⟩
      · rw [plsPpadsSucc_append hx₀_len hz₀_len]; dsimp only [plsPpadsSuccCore]
        have hstep₀' : C₁ (a, x) < C₁ (a, z.take (n₁ a)) := by rwa [hNx₀] at hstep₀
        simp only [hNx₀, decide_eq_true hstep₀', ↓reduceIte, binaryValue_binaryWord,
          decide_eq_false (Nat.lt_irrefl (2 ^ (n₁ a + n₂ a) - 2 ^ n₂ a)), Bool.false_eq_true,
          decide_true, decide_eq_true hi₀_lt, Bool.and_self, binaryWord_binaryValue hi₀_len,
          List.take_append_drop, (eq_zeroVertex_iff_binaryValue_eq_zero hr).mpr hk0]
      · rw [plsPpadsPotential_append hx₀_len hz₀_len, binaryValue_binaryWord, hk0, ← hNx₀, add_zero]
        exact plsPpadsPotential_jump_lt hstep₀ hBx₀
  · simp only [decide_eq_false hk0, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hc : (decide (binaryValue r ≤ 2 ^ (n₁ a + n₂ a) - 2 ^ n₂ a) &&
        decide (C₁ (a, N₁ (a, x)) < C₁ (a, x)))
    · simp [hc] at h
    · simp only [↓reduceIte] at h ⊢
      obtain ⟨hkM, hstep⟩ := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using hc
      have hk_sub_lt : binaryValue r - 1 < 2 ^ (n₁ a + n₂ a) - 2 ^ n₂ a := by omega
      have hk_add : binaryValue r - 1 + 1 = binaryValue r := by omega
      have gadget_pot {v : ℕ} (hv : v < 2 ^ (n₁ a + n₂ a)) :
          plsPpadsPotential n₁ C₁ n₂ B (a, x ++ (binaryWord (n₁ a + n₂ a) v ++
              binaryWord (n₁ a + n₂ a) (binaryValue r - 1))) <
            (B a - C₁ (a, x)) * 2 ^ (n₁ a + n₂ a) + binaryValue r := by
        rw [plsPpadsPotential_append hx (length_binaryWord hv), binaryValue_binaryWord]; omega
      by_cases hαK : binaryValue z + 1 < 2 ^ n₂ a
      · simp only [decide_eq_true hαK, ↓reduceIte] at h ⊢
        have hy'_len : (binaryWord (n₂ a) (binaryValue z + 1)).length = n₂ a :=
          length_binaryWord hαK
        cases hin : hasIn n₂ P₂ S₂ a (binaryWord (n₂ a) (binaryValue z + 1))
        · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hout : hasOut n₂ P₂ S₂ a (binaryWord (n₂ a) (binaryValue z + 1))
          · simp only [Bool.not_false, ↓reduceIte]
            have hy'_ne0 : binaryWord (n₂ a) (binaryValue z + 1) ≠ zeroVertex (n₂ a) := by
              rw [ne_eq, eq_zeroVertex_iff_binaryValue_eq_zero hy'_len, binaryValue_binaryWord]
              omega
            refine ⟨?_, gadget_pot (hαK.trans_le hKT)⟩
            rw [plsPpadsSucc_append hx (length_binaryWord (hαK.trans_le hKT))]
            dsimp only [plsPpadsSuccCore]
            simp only [decide_eq_true hstep, ↓reduceIte, binaryValue_binaryWord,
              decide_eq_true hk_sub_lt, decide_eq_true hαK, hout, Bool.false_eq_true,
              decide_eq_false hy'_ne0, hin, Bool.not_false, Bool.and_self,
              Nat.add_sub_cancel, hk_add, binaryWord_binaryValue hz,
              binaryWord_binaryValue hr]
          · simp only [hin, hout, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_self] at h
            exact absurd rfl h
        · simp only [↓reduceIte]
          have hin' := hin
          simp only [hasIn, decide_eq_true_eq] at hin'
          have hP_len := hP₂ _ hy'_len
          have hP_lt := binaryValue_lt_of_length hP_len
          refine ⟨?_, gadget_pot (hP_lt.trans_le hKT)⟩
          rw [plsPpadsSucc_append hx (length_binaryWord (hP_lt.trans_le hKT))]
          dsimp only [plsPpadsSuccCore]
          simp only [decide_eq_true hstep, ↓reduceIte, binaryValue_binaryWord,
            decide_eq_true hk_sub_lt, decide_eq_true hP_lt,
            binaryWord_binaryValue hP_len, hasOut_of_hasIn hin, hin'.1,
            Nat.add_sub_cancel, hk_add, binaryWord_binaryValue hz,
            binaryWord_binaryValue hr]
      · simp only [decide_eq_false hαK, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hαTk : binaryValue z < 2 ^ (n₁ a + n₂ a) - binaryValue r
        · simp only [decide_eq_true hαTk, ↓reduceIte]
          have hα1_lt : binaryValue z + 1 < 2 ^ (n₁ a + n₂ a) - (binaryValue r - 1) := by omega
          refine ⟨?_, gadget_pot (by omega)⟩
          rw [plsPpadsSucc_append hx (length_binaryWord (by omega))]
          dsimp only [plsPpadsSuccCore]
          simp only [decide_eq_true hstep, ↓reduceIte, binaryValue_binaryWord,
            decide_eq_true hk_sub_lt, decide_eq_false hαK, Bool.false_eq_true,
            decide_eq_true hα1_lt, Nat.add_sub_cancel, hk_add,
            binaryWord_binaryValue hz, binaryWord_binaryValue hr]
        · simp [decide_eq_false hαTk] at h

/-- No edge of the combined instance is pruned: `hasPotentialOut` holds iff `plsPpadsSucc` moves
the vertex. -/
theorem hasPotentialOut_plsPpads
    (hN₁ : ∀ u, u.length = n₁ a → (N₁ (a, u)).length = n₁ a)
    (hS₂ : ∀ u, u.length = n₂ a → (S₂ (a, u)).length = n₂ a)
    (hB : ∀ u, u.length = n₁ a → C₁ (a, u) < B a) {w : List Bool}
    (hw : w.length = plsPpadsWidth n₁ n₂ a) :
    hasPotentialOut (plsPpadsWidth n₁ n₂) (plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂)
        (plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂) (plsPpadsPotential n₁ C₁ n₂ B) a w = true ↔
      plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂ (a, w) ≠ w := by
  obtain ⟨x, z, r, rfl, hx, hz, hr⟩ := exists_append_three hw
  rw [hasPotentialOut_eq_true_iff]
  exact ⟨fun h => h.2.1, fun h =>
    let ⟨h₁, h₂, h₃⟩ := plsPpadsSucc_spec hx hz hr hN₁ hS₂ hB h
    ⟨h₁, h, h₂, h₃⟩⟩

/-- No edge of the combined instance is pruned: `hasPotentialIn` holds iff `plsPpadsPred` moves
the vertex. -/
theorem hasPotentialIn_plsPpads
    (hP₂ : ∀ u, u.length = n₂ a → (P₂ (a, u)).length = n₂ a)
    (hB : ∀ u, u.length = n₁ a → C₁ (a, u) < B a) {w : List Bool}
    (hw : w.length = plsPpadsWidth n₁ n₂ a) :
    hasPotentialIn (plsPpadsWidth n₁ n₂) (plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂)
        (plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂) (plsPpadsPotential n₁ C₁ n₂ B) a w = true ↔
      plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂ (a, w) ≠ w := by
  obtain ⟨x, z, r, rfl, hx, hz, hr⟩ := exists_append_three hw
  rw [hasPotentialIn_eq_true_iff]
  refine ⟨fun h => h.2.1, fun h => ?_⟩
  obtain ⟨h₁, h₂⟩ := plsPpadsPred_spec hx hz hr hP₂ hB h
  refine ⟨h₁, h, ?_, h₂⟩
  rw [ne_eq, append_three_eq_zeroVertex_iff hx hz]
  rintro ⟨rfl, rfl, rfl⟩
  have htake0 : (zeroVertex (n₁ a + n₂ a)).take (n₁ a) = zeroVertex (n₁ a) := by
    simp only [zeroVertex, List.take_replicate, Nat.min_eq_left (Nat.le_add_right _ _)]
  rw [plsPpadsPred_append hx hz] at h
  dsimp only [plsPpadsPredCore] at h
  simp only [binaryValue_zeroVertex, decide_true, ↓reduceIte, htake0] at h
  exact h (ite_eq_right_iff.mpr fun hc => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact absurd (hc.2 ▸ hc.1) (Nat.lt_irrefl _))

/-! ### Decoding sinks of the combined instance -/

/-- **Sinks of the combined instance decode to solutions**
[Göös et al., Section 4, Lemma 3][GoosEtAl2022]: any sink `x ++ (z ++ r)` of the combined
sink-of-potential-line instance yields either a local optimum of `(n₁, N₁, C₁)` at `x` or a
sink-of-line solution of `(n₂, P₂, S₂)` at `binaryWord (n₂ a) (binaryValue z)`. -/
theorem plsPpads_sink
    (hN₁ : ∀ u, u.length = n₁ a → (N₁ (a, u)).length = n₁ a)
    (hP₂ : ∀ u, u.length = n₂ a → (P₂ (a, u)).length = n₂ a)
    (hS₂ : ∀ u, u.length = n₂ a → (S₂ (a, u)).length = n₂ a)
    (hB : ∀ u, u.length = n₁ a → C₁ (a, u) < B a)
    (hx : x.length = n₁ a) (hz : z.length = n₁ a + n₂ a) (hr : r.length = n₁ a + n₂ a)
    (h : sinkOfPotentialLineRel (plsPpadsWidth n₁ n₂)
      (plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂) (plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂)
      (plsPpadsPotential n₁ C₁ n₂ B) a (x ++ (z ++ r))) :
    localOptRel n₁ N₁ C₁ a x ∨
      sinkOfLineRel n₂ P₂ S₂ a (binaryWord (n₂ a) (binaryValue z)) := by
  by_cases hstep : C₁ (a, N₁ (a, x)) < C₁ (a, x)
  · right
    have hw : (x ++ (z ++ r)).length = plsPpadsWidth n₁ n₂ a := by
      simp only [plsPpadsWidth, List.length_append, hx, hz, hr]; omega
    have hout_false : plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂ (a, x ++ (z ++ r)) = x ++ (z ++ r) :=
      not_ne_iff.mp fun hne => Bool.false_ne_true
        (h.2.1.symm.trans ((hasPotentialOut_plsPpads hN₁ hS₂ hB hw).mpr hne))
    rw [plsPpadsSucc_append hx hz] at hout_false
    have hn₁_pos : 0 < n₁ a := Nat.pos_of_ne_zero fun hn0 => by
      rw [List.length_eq_zero_iff.mp ((hN₁ x hx).trans hn0),
        List.length_eq_zero_iff.mp (hx.trans hn0)] at hstep
      exact Nat.lt_irrefl _ hstep
    have hM_pos : 0 < 2 ^ (n₁ a + n₂ a) - 2 ^ n₂ a :=
      Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    have hαT := binaryValue_lt_of_length hz
    have hKT := two_pow_le_two_pow_add (n₁ a) (n₂ a)
    -- Step 1: every active incoming edge (or `0 ^ W`) lands at `k < M` and `α < T - k`.
    obtain ⟨hkM, hαTk⟩ : binaryValue r < 2 ^ (n₁ a + n₂ a) - 2 ^ n₂ a ∧
        binaryValue z < 2 ^ (n₁ a + n₂ a) - binaryValue r := by
      rcases h.2.2 with hz0 | hin
      · obtain ⟨-, rfl, rfl⟩ := (append_three_eq_zeroVertex_iff hx hz).mp hz0
        simp only [binaryValue_zeroVertex, Nat.sub_zero]
        exact ⟨hM_pos, Nat.two_pow_pos (n₁ a + n₂ a)⟩
      · have hpred_ne := (hasPotentialIn_plsPpads hP₂ hB hw).mp hin
        rw [plsPpadsPred_append hx hz] at hpred_ne
        dsimp only [plsPpadsPredCore] at hpred_ne
        by_cases hk0 : binaryValue r = 0
        · exact ⟨by omega, by omega⟩
        · simp only [decide_eq_false hk0, Bool.false_eq_true, ↓reduceIte] at hpred_ne
          have hkM_le : binaryValue r ≤ 2 ^ (n₁ a + n₂ a) - 2 ^ n₂ a := by
            by_contra hgt; simp [decide_eq_false hgt] at hpred_ne
          have hαTk : binaryValue z < 2 ^ (n₁ a + n₂ a) - binaryValue r := by
            by_cases hαK : binaryValue z + 1 < 2 ^ n₂ a
            · omega
            · simp only [decide_eq_true hkM_le, decide_eq_true hstep, Bool.and_self,
                ↓reduceIte, decide_eq_false hαK, Bool.false_eq_true] at hpred_ne
              by_contra hge; simp [decide_eq_false hge] at hpred_ne
          have hk_ne_M : binaryValue r ≠ 2 ^ (n₁ a + n₂ a) - 2 ^ n₂ a := by
            intro hk_eq
            have hαK : binaryValue z < 2 ^ n₂ a := by omega
            dsimp only [plsPpadsSuccCore] at hout_false
            simp only [decide_eq_true hstep, ↓reduceIte, hk_eq, Nat.lt_irrefl, decide_false,
              Bool.false_eq_true, decide_true, decide_eq_true hαK, Bool.and_self] at hout_false
            have hNx_eq := (append_three_inj (hN₁ x hx)
              (by simp [hx, length_binaryWord hαK]) hx hz hout_false).1
            exact Nat.lt_irrefl _ (hNx_eq ▸ hstep)
          exact ⟨by omega, hαTk⟩
    -- Helper: any branch producing `binaryWord m (k + 1)` in `r` contradicts `hout_false`.
    have no_step_r {v : ℕ} (hv : v < 2 ^ (n₁ a + n₂ a))
        (heq : x ++ (binaryWord (n₁ a + n₂ a) v ++
          binaryWord (n₁ a + n₂ a) (binaryValue r + 1)) = x ++ (z ++ r)) : False := by
      have hval := congrArg binaryValue
        (append_three_inj hx (length_binaryWord hv) hx hz heq).2.2
      rw [binaryValue_binaryWord] at hval; omega
    dsimp only [plsPpadsSuccCore] at hout_false
    simp only [decide_eq_true hstep, decide_eq_true hkM, ↓reduceIte] at hout_false
    -- Step 2: `α < K` must hold, else the shift branch advances `k` to `k + 1`.
    have hαK : binaryValue z < 2 ^ n₂ a := by
      by_contra hge
      simp only [decide_eq_false hge, Bool.false_eq_true, ↓reduceIte,
        decide_eq_true hαTk] at hout_false
      exact no_step_r (by omega) hout_false
    simp only [decide_eq_true hαK, ↓reduceIte] at hout_false
    have hy_len : (binaryWord (n₂ a) (binaryValue z)).length = n₂ a := length_binaryWord hαK
    -- Step 3: neither `hasOut` nor the isolated non-zero hole-self-map branch can fire.
    have hy_out : hasOut n₂ P₂ S₂ a (binaryWord (n₂ a) (binaryValue z)) = false := by
      by_contra ho
      simp only [Bool.eq_true_of_not_eq_false ho, ↓reduceIte] at hout_false
      have := binaryValue_lt_of_length (hS₂ _ hy_len)
      exact no_step_r (by omega) hout_false
    simp only [hy_out, Bool.false_eq_true, ↓reduceIte] at hout_false
    refine ⟨hy_len, hy_out, ?_⟩
    by_contra hc
    push Not at hc
    simp only [decide_eq_false hc.1, hc.2, Bool.not_false, Bool.and_self, ↓reduceIte] at hout_false
    exact no_step_r (by omega) hout_false
  · exact Or.inl ⟨hx, Nat.not_lt.mp hstep⟩

/-! ### Lengths and polynomial-time computability -/

private theorem length_plsPpads_triple {n₁ n₂ : ℕ} {u v s : List Bool}
    (hu : u.length = n₁) (hv : v.length = n₁ + n₂) (hs : s.length = n₁ + n₂) :
    (u ++ (v ++ s)).length = n₁ + (n₁ + n₂) + (n₁ + n₂) := by
  simp only [List.length_append, hu, hv, hs]; omega

theorem length_plsPpadsSucc
    (hN₁ : ∀ u, u.length = n₁ a → (N₁ (a, u)).length = n₁ a)
    (hS₂ : ∀ u, u.length = n₂ a → (S₂ (a, u)).length = n₂ a) {w : List Bool}
    (hw : w.length = plsPpadsWidth n₁ n₂ a) :
    (plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂ (a, w)).length = plsPpadsWidth n₁ n₂ a := by
  obtain ⟨x, z, r, rfl, hx, hz, hr⟩ := exists_append_three hw
  rw [plsPpadsSucc_append hx hz]
  have : binaryValue z < 2 ^ (n₁ a + n₂ a) ∧ binaryValue r < 2 ^ (n₁ a + n₂ a) ∧
      2 ^ n₂ a ≤ 2 ^ (n₁ a + n₂ a) ∧ 0 < 2 ^ n₂ a :=
    ⟨binaryValue_lt_of_length hz, binaryValue_lt_of_length hr,
      two_pow_le_two_pow_add (n₁ a) (n₂ a), Nat.two_pow_pos (n₂ a)⟩
  dsimp only [plsPpadsSuccCore]
  refine length_ite_bool (fun _ => ?_) (fun _ => hw)
  refine length_ite_bool (fun hkM => ?_) (fun _ =>
    length_ite_bool (fun hMα => ?_) (fun _ => hw))
  · have hkM' := of_decide_eq_true hkM
    have hstep {v : ℕ} (hv : v < 2 ^ (n₁ a + n₂ a)) :
        (x ++ (binaryWord (n₁ a + n₂ a) v ++
          binaryWord (n₁ a + n₂ a) (binaryValue r + 1))).length = plsPpadsWidth n₁ n₂ a :=
      length_plsPpads_triple hx (length_binaryWord hv) (length_binaryWord (by omega))
    refine length_ite_bool (fun hαK => ?_) (fun _ =>
      length_ite_bool (fun _ => hstep (by omega)) (fun _ => hw))
    refine length_ite_bool (fun _ => ?_) (fun _ =>
      length_ite_bool (fun _ => hstep (by omega)) (fun _ => hw))
    have hS_lt := binaryValue_lt_of_length (hS₂ _ (length_binaryWord (of_decide_eq_true hαK)))
    exact hstep (by omega)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hMα
    exact length_plsPpads_triple (hN₁ x hx)
      (by simp [hx, length_binaryWord hMα.2]) (length_zeroVertex _)

theorem length_plsPpadsPred
    (hP₂ : ∀ u, u.length = n₂ a → (P₂ (a, u)).length = n₂ a) {w : List Bool}
    (hw : w.length = plsPpadsWidth n₁ n₂ a) :
    (plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂ (a, w)).length = plsPpadsWidth n₁ n₂ a := by
  obtain ⟨x, z, r, rfl, hx, hz, hr⟩ := exists_append_three hw
  rw [plsPpadsPred_append hx hz]
  have hkT := binaryValue_lt_of_length hr
  have hKT := two_pow_le_two_pow_add (n₁ a) (n₂ a)
  have hMT := two_pow_sub_lt (n₁ a) (n₂ a)
  dsimp only [plsPpadsPredCore]
  refine length_ite_bool (fun _ => ?_) (fun hk0 => ?_)
  · refine length_ite_bool (fun _ => ?_) (fun _ => hw)
    have hi₀_len : (z.drop (n₁ a)).length = n₂ a := by simp only [List.length_drop, hz]; omega
    exact length_plsPpads_triple (by simp only [List.length_take, hz]; omega)
      (length_binaryWord ((binaryValue_lt_of_length hi₀_len).trans_le hKT))
      (length_binaryWord hMT)
  · refine length_ite_bool (fun _ => ?_) (fun _ => hw)
    have hstep {v : ℕ} (hv : v < 2 ^ (n₁ a + n₂ a)) :
        (x ++ (binaryWord (n₁ a + n₂ a) v ++
          binaryWord (n₁ a + n₂ a) (binaryValue r - 1))).length = plsPpadsWidth n₁ n₂ a :=
      length_plsPpads_triple hx (length_binaryWord hv) (length_binaryWord (by omega))
    refine length_ite_bool (fun hαK => ?_) (fun _ =>
      length_ite_bool (fun hαTk => ?_) (fun _ => hw))
    · refine length_ite_bool (fun _ => hstep
          ((binaryValue_lt_of_length
            (hP₂ _ (length_binaryWord (of_decide_eq_true hαK)))).trans_le hKT))
        (fun _ => length_ite_bool (fun _ => hstep ((of_decide_eq_true hαK).trans_le hKT))
          (fun _ => hw))
    · have : binaryValue r ≠ 0 ∧ binaryValue z < 2 ^ (n₁ a + n₂ a) - binaryValue r :=
        ⟨of_decide_eq_false hk0, of_decide_eq_true hαTk⟩
      exact hstep (by omega)

section Computability

variable {enc : α ↪ List Bool}

attribute [local fun_prop, local program_certificate] binaryWord_polyTime

theorem computableInPolyTime_plsPpadsSucc
    (hn₁ : ComputableInPolyTime n₁ enc encUnary)
    (hN₁ : ComputableInPolyTime N₁ (encPair enc encBits) encBits)
    (hC₁ : ComputableInPolyTime C₁ (encPair enc encBits) encNat)
    (hn₂ : ComputableInPolyTime n₂ enc encUnary)
    (hP₂ : ComputableInPolyTime P₂ (encPair enc encBits) encBits)
    (hS₂ : ComputableInPolyTime S₂ (encPair enc encBits) encBits) :
    ComputableInPolyTime (plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂) (encPair enc encBits) encBits := by
  polytime [plsPpadsSucc, plsPpadsSuccCore]

theorem computableInPolyTime_plsPpadsPred
    (hn₁ : ComputableInPolyTime n₁ enc encUnary)
    (hN₁ : ComputableInPolyTime N₁ (encPair enc encBits) encBits)
    (hC₁ : ComputableInPolyTime C₁ (encPair enc encBits) encNat)
    (hn₂ : ComputableInPolyTime n₂ enc encUnary)
    (hP₂ : ComputableInPolyTime P₂ (encPair enc encBits) encBits)
    (hS₂ : ComputableInPolyTime S₂ (encPair enc encBits) encBits) :
    ComputableInPolyTime (plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂) (encPair enc encBits) encBits := by
  polytime [plsPpadsPred, plsPpadsPredCore]

theorem computableInPolyTime_plsPpadsPotential
    (hn₁ : ComputableInPolyTime n₁ enc encUnary)
    (hC₁ : ComputableInPolyTime C₁ (encPair enc encBits) encNat)
    (hn₂ : ComputableInPolyTime n₂ enc encUnary)
    (hB : ComputableInPolyTime B enc encNat) :
    ComputableInPolyTime (plsPpadsPotential n₁ C₁ n₂ B) (encPair enc encBits) encNat := by
  fun_prop [plsPpadsPotential]

end Computability

/-! ### `PLS ∩ PPADS ⊆ SOPL`, `SOPL = PLS ∩ PPADS`, and `EOPL = PLS ∩ PPAD` -/

section Collapse

variable {enc : α ↪ List Bool} {R : α → List Bool → Prop}

attribute [local fun_prop] binaryWord_polyTime

/-- A problem in `FNP` whose solutions can be read back, on the same instance, from the local
optima of a uniform polynomial-time local-search family and from the sinks of a uniform
polynomial-time sink-of-line family lies in `SOPL`
[Göös et al., Section 4, Lemma 3][GoosEtAl2022]. -/
theorem mem_SOPL_of_localOpt_sinkOfLine (hR : R ∈ FNP enc)
    (hn₁ : ComputableInPolyTime n₁ enc encUnary)
    (hN₁ : ComputableInPolyTime N₁ (encPair enc encBits) encBits)
    (hC₁ : ComputableInPolyTime C₁ (encPair enc encBits) encNat)
    (hN₁_len : PreservesWidth n₁ N₁)
    (hn₂ : ComputableInPolyTime n₂ enc encUnary)
    (hP₂ : ComputableInPolyTime P₂ (encPair enc encBits) encBits)
    (hS₂ : ComputableInPolyTime S₂ (encPair enc encBits) encBits)
    (hP₂_len : PreservesWidth n₂ P₂) (hS₂_len : PreservesWidth n₂ S₂)
    {g₁ g₂ : α × List Bool → List Bool}
    (hg₁ : ComputableInPolyTime g₁ (encPair enc encBits) encBits)
    (hg₂ : ComputableInPolyTime g₂ (encPair enc encBits) encBits)
    (h₁ : ∀ a w, localOptRel n₁ N₁ C₁ a w → R a (g₁ (a, w)))
    (h₂ : ∀ a w, sinkOfLineRel n₂ P₂ S₂ a w → R a (g₂ (a, w))) :
    R ∈ SOPL enc := by
  obtain ⟨m₀, hm₀, hB⟩ := exists_potentialBound hn₁ hC₁
  let g (p : α × List Bool) : List Bool :=
    if decide (C₁ (p.1, p.2.take (n₁ p.1)) ≤ C₁ (p.1, N₁ (p.1, p.2.take (n₁ p.1)))) then
      g₁ (p.1, p.2.take (n₁ p.1))
    else g₂ (p.1, binaryWord (n₂ p.1)
      (binaryValue ((p.2.drop (n₁ p.1)).take (n₁ p.1 + n₂ p.1))))
  have hg : ComputableInPolyTime g (encPair enc encBits) encBits := by
    dsimp only [g]
    fun_prop
  have hSucc_len : PreservesWidth (plsPpadsWidth n₁ n₂) (plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂) :=
    fun a _ hw => length_plsPpadsSucc (hN₁_len a) (hS₂_len a) hw
  have hPred_len : PreservesWidth (plsPpadsWidth n₁ n₂) (plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂) :=
    fun a _ hw => length_plsPpadsPred (hP₂_len a) hw
  refine ⟨hR, plsPpadsWidth n₁ n₂, plsPpadsPred n₁ N₁ C₁ n₂ P₂ S₂,
    plsPpadsSucc n₁ N₁ C₁ n₂ P₂ S₂, plsPpadsPotential n₁ C₁ n₂ (fun a => 2 ^ m₀ a),
    by fun_prop [plsPpadsWidth],
    computableInPolyTime_plsPpadsPred hn₁ hN₁ hC₁ hn₂ hP₂ hS₂,
    computableInPolyTime_plsPpadsSucc hn₁ hN₁ hC₁ hn₂ hP₂ hS₂,
    computableInPolyTime_plsPpadsPotential hn₁ hC₁ hn₂ (by fun_prop), hPred_len, hSucc_len,
    .of_isTotalSearch (isTotalSearch_sinkOfPotentialLineRel hSucc_len) ComputableInPolyTime.id' hg
      fun a w hw => ?_⟩
  obtain ⟨x, z, r, rfl, hx, hz, hr⟩ := exists_append_three hw.1
  have hsink := plsPpads_sink (hN₁_len a) (hP₂_len a) (hS₂_len a) (hB a) hx hz hr hw
  dsimp only [g]
  simp only [List.take_left' hx, List.drop_left' hx, List.take_left' hz]
  split_ifs with hc
  · exact h₁ _ _ ⟨hx, decide_eq_true_eq.mp hc⟩
  · exact h₂ _ _ (hsink.resolve_left fun hopt => hc (decide_eq_true_eq.mpr hopt.2))

/-- **`PLS ∩ PPADS ⊆ SOPL`** [Göös et al., Section 4, Lemma 3][GoosEtAl2022]. -/
theorem PLS_inter_PPADS_subset_SOPL : PLS enc ∩ PPADS enc ⊆ SOPL enc := by
  rintro R ⟨⟨hR, n₁, N₁, C₁, hn₁, hN₁, hC₁, hN₁_len, f₁, g₁, hf₁, hg₁, -, h₁⟩,
    ⟨-, n₂, P₂, S₂, hn₂, hP₂, hS₂, hP₂_len, hS₂_len, f₂, g₂, hf₂, hg₂, -, h₂⟩⟩
  have hpair₁ := (hf₁.comp (.fst enc encBits)).prod (.snd enc encBits)
  have hpair₂ := (hf₂.comp (.fst enc encBits)).prod (.snd enc encBits)
  exact mem_SOPL_of_localOpt_sinkOfLine (n₁ := n₁ ∘ f₁) (N₁ := fun p => N₁ (f₁ p.1, p.2))
    (C₁ := fun p => C₁ (f₁ p.1, p.2)) (n₂ := n₂ ∘ f₂) (P₂ := fun p => P₂ (f₂ p.1, p.2))
    (S₂ := fun p => S₂ (f₂ p.1, p.2)) hR (hn₁.comp hf₁) (hN₁.comp hpair₁) (hC₁.comp hpair₁)
    (fun a => hN₁_len (f₁ a)) (hn₂.comp hf₂) (hP₂.comp hpair₂) (hS₂.comp hpair₂)
    (fun a => hP₂_len (f₂ a)) (fun a => hS₂_len (f₂ a)) hg₁ hg₂ h₁ h₂

/-- **`SOPL = PLS ∩ PPADS`** [Göös et al., Theorem 2][GoosEtAl2022]. -/
theorem SOPL_eq_PLS_inter_PPADS : SOPL enc = PLS enc ∩ PPADS enc :=
  Set.Subset.antisymm SOPL_subset_PLS_inter_PPADS PLS_inter_PPADS_subset_SOPL

/-- **`PLS ∩ PPAD ⊆ EOPL`** [Göös et al., Theorem 1][GoosEtAl2022], via `PPAD ⊆ PPADS`,
`PLS ∩ PPADS ⊆ SOPL`, and `SOPL ∩ PPAD ⊆ EOPL`. -/
theorem PLS_inter_PPAD_subset_EOPL : PLS enc ∩ PPAD enc ⊆ EOPL enc :=
  fun _ ⟨hPLS, hPPAD⟩ =>
    SOPL_inter_PPAD_subset_EOPL ⟨PLS_inter_PPADS_subset_SOPL ⟨hPLS, PPAD_subset_PPADS hPPAD⟩,
      hPPAD⟩

/-- **`EOPL = PLS ∩ PPAD`** [Göös et al., Theorem 1][GoosEtAl2022]. -/
theorem EOPL_eq_PLS_inter_PPAD : EOPL enc = PLS enc ∩ PPAD enc :=
  Set.Subset.antisymm EOPL_subset_PLS_inter_PPAD PLS_inter_PPAD_subset_EOPL

end Collapse

end Cslib.Complexity
