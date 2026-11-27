/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Nondeterministic.CoverNumber
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.List.Infix

/-!
# Nondeterministic multi-pass streaming algorithms give covers

A **nondeterministic multi-pass streaming algorithm**
(`Cslib.Streaming.Nondeterministic.Algorithm σ α β`) reads the stream several times from left to
right, like a deterministic one (`Cslib.Streaming.MultiPass`), but each update and each transition
at the end of a pass may lead to any of a set of memory states. Its memory is measured as in the
deterministic case: `A.SpaceLE p m b` says that the states held between items by some computation
during `p` passes over streams of at most `m` items have an injective `b`-bit encoding.

A function `f` is decided with answer `z` when, on the stream `u x ++ v y`, `f x y = z` holds
exactly when some computation of `p` passes ends in a state whose answer `d` maps to `z`. For
`z = true` this is a nondeterministic algorithm, which accepts when some computation accepts; for
`z = false` it is a co-nondeterministic one, which rejects when some computation rejects.
Computations that get stuck (an empty set of successors) neither accept nor reject, as usual for
nondeterministic machines; so $N^0(f)$ is $N^1$ of the negation of `f`.

**Covers.** For $p \ge 1$ passes, a computation on `u x ++ v y` is determined, as far as the two
players are concerned, by the $2p-1$ memory states at the boundaries between `u x` and `v y`: the
state after Alice's part of each pass, and the state at the start of each later pass. For a guess of
these states, the inputs `x` whose parts of the passes connect them form a set, and so do the inputs
`y`; their product is a rectangle on which `f` is `z`, and every pair with `f x y = z` lies in the
rectangle of the boundary states of an accepting computation. So `f` has a `z`-cover by
$2^{(2p-1)b}$ rectangles, and nondeterministic complexity at most $(2p-1)b$
(`Cslib.Streaming.Nondeterministic.Algorithm.ecomplexityFun_le_of_spaceLE`). Unlike the
deterministic simulation (`Cslib.Streaming.MultiPass.ecomplexityFun_le_of_spaceLE`), no final bit is
needed: the cover is checked, not computed. This adapts the one-pass reduction of Alon, Matias and
Szegedy [AlonMatiasSzegedy1999, Section 3] to `p` passes and to nondeterministic algorithms, with
nondeterministic communication complexity defined by covers as in
`Cslib.Communication.Nondeterministic`. For one pass, Das, Fraigniaud, Paz and Rosén give the
corresponding bound for streaming certification schemes, in which the algorithm receives a
certificate before the stream [DasFraigniaudPazRosen2025, Lemma 7].

## Main definitions

* `Cslib.Streaming.Nondeterministic.Algorithm`: nondeterministic multi-pass streaming algorithms,
  with `Cslib.Streaming.Nondeterministic.Algorithm.passes` (the states after `k` passes) and
  `Cslib.Streaming.Nondeterministic.Algorithm.answers`.
* `Cslib.Streaming.Nondeterministic.Algorithm.reachable`,
  `Cslib.Streaming.Nondeterministic.Algorithm.SpaceLE`: the states reached during `p` passes, and
  memory bounds.

## Main results

* `Cslib.Streaming.Nondeterministic.Algorithm.mem_passes_iff_exists_chain`: the states after `k`
  passes over `s ++ t` are those reached through a chain of boundary states.
* `Cslib.Streaming.Nondeterministic.Algorithm.ecomplexityFun_le_of_spaceLE`: `p`-pass
  nondeterministic streaming memory `b` bounds nondeterministic communication by $(2p-1)b$.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Section 3][AlonMatiasSzegedy1999]
* [A. Das, P. Fraigniaud, A. Paz, A. Rosén, *Semi-streaming algorithms for graph property
  certification*, Lemma 7][DasFraigniaudPazRosen2025]
-/

public section

namespace Cslib.Streaming.Nondeterministic

/-- A **nondeterministic multi-pass streaming algorithm** over items of type `α` with answers in
`β`: memory states `σ`, an initial state, the possible states after reading one more item, the
possible states at the start of the next pass given the state at the end of a pass, and an answer
for each state. -/
structure Algorithm (σ α β : Type*) where
  /-- The initial memory state. -/
  init : σ
  /-- The possible memory states after reading one more item. -/
  update : σ → α → Set σ
  /-- The possible memory states at the start of the next pass. -/
  endPass : σ → Set σ
  /-- The answer reported in a memory state. -/
  output : σ → β

namespace Algorithm

variable {σ α β : Type*} (A : Algorithm σ α β)

/-- The possible memory states after reading the stream `s` from `q`. -/
@[expose] def statesFrom : σ → List α → Set σ
  | q, [] => {q}
  | q, a :: s => ⋃ q' ∈ A.update q a, statesFrom q' s

/-- The possible memory states after one pass over `s` from `q`, including `endPass`. -/
@[expose] def pass (s : List α) (q : σ) : Set σ :=
  ⋃ q' ∈ A.statesFrom q s, A.endPass q'

/-- The possible memory states after `k` passes over `s`. -/
@[expose] def passes (s : List α) : ℕ → Set σ
  | 0 => {A.init}
  | k + 1 => ⋃ q ∈ passes s k, A.pass s q

/-- The possible answers after `p` passes over `s`. -/
@[expose] def answers (p : ℕ) (s : List α) : Set β :=
  A.output '' A.passes s p

@[simp] theorem mem_statesFrom_nil {q q' : σ} : q' ∈ A.statesFrom q [] ↔ q' = q :=
  Iff.rfl

theorem mem_statesFrom_append {q q'' : σ} {s t : List α} :
    q'' ∈ A.statesFrom q (s ++ t) ↔ ∃ q' ∈ A.statesFrom q s, q'' ∈ A.statesFrom q' t := by
  induction s generalizing q with
  | nil => simp
  | cons a s ih =>
    simp only [List.cons_append, statesFrom, Set.mem_iUnion, ih, exists_prop]
    constructor
    · rintro ⟨i, hi, q', hq', h⟩
      exact ⟨q', ⟨i, hi, hq'⟩, h⟩
    · rintro ⟨q', ⟨i, hi, hq'⟩, h⟩
      exact ⟨i, hi, q', hq', h⟩

theorem mem_pass {q q' : σ} {s : List α} :
    q' ∈ A.pass s q ↔ ∃ q'' ∈ A.statesFrom q s, q' ∈ A.endPass q'' := by
  simp only [pass, Set.mem_iUnion, exists_prop]

/-- A pass over `s ++ t` is a pass over `s` continued on `t`. -/
theorem mem_pass_append {q q'' : σ} {s t : List α} :
    q'' ∈ A.pass (s ++ t) q ↔ ∃ q' ∈ A.statesFrom q s, q'' ∈ A.pass t q' := by
  simp only [mem_pass, mem_statesFrom_append]
  constructor
  · rintro ⟨r, ⟨q', hq', hr⟩, h⟩
    exact ⟨q', hq', r, hr, h⟩
  · rintro ⟨q', hq', r, hr, h⟩
    exact ⟨r, ⟨q', hq', hr⟩, h⟩

@[simp] theorem mem_passes_zero {s : List α} {q : σ} : q ∈ A.passes s 0 ↔ q = A.init :=
  Iff.rfl

theorem mem_passes_succ {s : List α} {k : ℕ} {q : σ} :
    q ∈ A.passes s (k + 1) ↔ ∃ q' ∈ A.passes s k, q ∈ A.pass s q' := by
  simp only [passes, Set.mem_iUnion, exists_prop]

/-- **Boundary states.** A state is possible after `k` passes over `s ++ t` exactly when it ends a
chain of states `st 0 = init, mid 0, st 1, …, mid (k - 1), st k` in which each `mid j` is possible
after reading `s` from `st j`, and each `st (j + 1)` after finishing the pass on `t` from
`mid j`. -/
theorem mem_passes_iff_exists_chain {s t : List α} {k : ℕ} {q : σ} :
    q ∈ A.passes (s ++ t) k ↔ ∃ st mid : ℕ → σ, st 0 = A.init ∧ st k = q ∧
      ∀ j < k, mid j ∈ A.statesFrom (st j) s ∧ st (j + 1) ∈ A.pass t (mid j) := by
  induction k generalizing q with
  | zero =>
    refine ⟨fun h => ⟨fun _ => A.init, fun _ => A.init, rfl, h.symm,
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩, ?_⟩
    rintro ⟨st, mid, h0, rfl, -⟩
    exact h0
  | succ k ih =>
    rw [mem_passes_succ]
    constructor
    · rintro ⟨q₀, hq₀, hq⟩
      obtain ⟨r, hr, hq⟩ := A.mem_pass_append.1 hq
      obtain ⟨st, mid, h0, hk, hchain⟩ := ih.1 hq₀
      refine ⟨Function.update st (k + 1) q, Function.update mid k r, ?_, by simp, fun j hj => ?_⟩
      · rw [Function.update_of_ne (by omega)]
        exact h0
      · rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj | rfl
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hchain j hj
        · rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self, hk]
          exact ⟨hr, hq⟩
    · rintro ⟨st, mid, h0, rfl, hchain⟩
      refine ⟨st k, ih.2 ⟨st, mid, h0, rfl, fun j hj => hchain j (by omega)⟩, ?_⟩
      obtain ⟨hmid, hst⟩ := hchain k (by omega)
      exact A.mem_pass_append.2 ⟨mid k, hmid, hst⟩

/-- The memory states reachable during `p` passes over streams of length at most `m`: the states
possible between items during each pass, from its start to its end (before `endPass`). -/
@[expose] def reachable (p m : ℕ) : Set σ :=
  {q | ∃ s : List α, s.length ≤ m ∧
    ∃ k < p, ∃ t, t <+: s ∧ ∃ q₀ ∈ A.passes s k, q ∈ A.statesFrom q₀ t}

/-- `A` **uses at most `b` bits of memory during `p` passes over streams of length at most `m`**:
the memory states it can reach have an injective encoding by `b`-bit strings. -/
@[expose] def SpaceLE (p m b : ℕ) : Prop :=
  ∃ enc : σ → BitString b, Set.InjOn enc (A.reachable p m)

theorem mem_reachable_of_statesFrom {p m k : ℕ} {s t : List α} {q₀ q : σ} (hs : s.length ≤ m)
    (hk : k < p) (ht : t <+: s) (hq₀ : q₀ ∈ A.passes s k) (hq : q ∈ A.statesFrom q₀ t) :
    q ∈ A.reachable p m :=
  ⟨s, hs, k, hk, t, ht, q₀, hq₀, hq⟩

theorem mem_reachable_of_passes {p m k : ℕ} {s : List α} {q : σ} (hs : s.length ≤ m) (hk : k < p)
    (hq : q ∈ A.passes s k) : q ∈ A.reachable p m :=
  A.mem_reachable_of_statesFrom hs hk List.nil_prefix hq rfl

/-- Decoding a `b`-bit guess: the reachable state that `enc` maps to it, if any. -/
noncomputable def decode (p m b : ℕ) (enc : σ → BitString b) (w : BitString b) : σ :=
  haveI : Nonempty σ := ⟨A.init⟩
  Function.invFunOn enc (A.reachable p m) w

theorem decode_enc {p m b : ℕ} {enc : σ → BitString b} (henc : Set.InjOn enc (A.reachable p m))
    {q : σ} (hq : q ∈ A.reachable p m) : A.decode p m b enc (enc q) = q :=
  haveI : Nonempty σ := ⟨A.init⟩
  henc.leftInvOn_invFunOn hq

/-- The state at the start of pass `j` in the guess `w` for `n + 1` passes: the initial state for
the first pass, and the decoding of Bob's `j - 1`-th guess for the others. -/
private noncomputable def start (p m b n : ℕ) (enc : σ → BitString b)
    (w : (Fin (n + 1) → BitString b) × (Fin n → BitString b)) (j : ℕ) : σ :=
  if h : j - 1 < n ∧ j ≠ 0 then A.decode p m b enc (w.2 ⟨j - 1, h.1⟩) else A.init

private theorem start_zero (p m b n : ℕ) (enc : σ → BitString b)
    (w : (Fin (n + 1) → BitString b) × (Fin n → BitString b)) :
    start A p m b n enc w 0 = A.init := by
  simp [start]

private theorem start_succ (p m b n : ℕ) (enc : σ → BitString b)
    (w : (Fin (n + 1) → BitString b) × (Fin n → BitString b)) {j : ℕ} (hj : j < n) :
    start A p m b n enc w (j + 1) = A.decode p m b enc (w.2 ⟨j, hj⟩) := by
  simp [start, hj]

variable {X Y : Type*}

open Communication Nondeterministic

/-- **Nondeterministic multi-pass streaming space bounds nondeterministic communication**: if, for
$p \ge 1$, a nondeterministic `p`-pass streaming algorithm with `b` bits of memory on streams of
length at most `m` decides `f` with answer `z` on the streams `u x ++ v y`, which have length at
most `m`, that is, `f x y = z` exactly when some computation ends in a state whose answer `d` maps
to `z`, then the `z`-nondeterministic complexity of `f` is at most $(2p-1)b$. For `z = true` the
algorithm is nondeterministic and the bound is on `N¹`; for `z = false` it is co-nondeterministic
and the bound is on `N⁰`. -/
theorem ecomplexityFun_le_of_spaceLE {p m b : ℕ} (hp : 0 < p) (hA : A.SpaceLE p m b)
    (u : X → List α) (v : Y → List α) (hm : ∀ x y, (u x ++ v y).length ≤ m) (d : β → Bool)
    (z : Bool) (f : X → Y → Bool)
    (hf : ∀ x y, f x y = z ↔ ∃ c ∈ A.answers p (u x ++ v y), d c = z) :
    ecomplexityFun z f Set.univ Set.univ ≤ ((2 * p - 1) * b : ℕ) := by
  classical
  obtain ⟨enc, henc⟩ := hA
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  set dec := A.decode (n + 1) m b enc with hdec
  let C : (Fin (n + 1) → BitString b) × (Fin n → BitString b) → Set X × Set Y := fun w =>
    ({x | ∀ k : Fin (n + 1), dec (w.1 k) ∈ A.statesFrom (start A (n + 1) m b n enc w k) (u x)},
      {y | (∀ k : Fin n, dec (w.2 k) ∈ A.pass (v y) (dec (w.1 k.castSucc))) ∧
        ∃ q ∈ A.pass (v y) (dec (w.1 (Fin.last n))), d (A.output q) = z})
  have hC : IsCover z (fun x y c => f x y = c) Set.univ Set.univ C := by
    refine isCover_fun_iff.2 ⟨fun w x _ hx y _ ⟨hy, q, hq, hqz⟩ => ?_, fun x _ y _ hxy => ?_⟩
    · -- Soundness: the guessed boundary states are those of a computation.
      have key : ∀ j ≤ n, start A (n + 1) m b n enc w j ∈ A.passes (u x ++ v y) j := by
        intro j hj
        induction j with
        | zero => rw [start_zero]; rfl
        | succ j ih =>
          rw [start_succ A _ _ _ _ _ _ (by omega : j < n), A.mem_passes_succ]
          refine ⟨_, ih (by omega), A.mem_pass_append.2 ⟨_, hx ⟨j, by omega⟩, ?_⟩⟩
          exact hy ⟨j, by omega⟩
      refine (hf x y).2 ⟨A.output q, ⟨q, A.mem_passes_succ.2 ⟨_, key n le_rfl,
        A.mem_pass_append.2 ⟨_, hx (Fin.last n), hq⟩⟩, rfl⟩, hqz⟩
    · -- Completeness: the boundary states of an accepting computation form a guess.
      obtain ⟨c, ⟨q, hq, rfl⟩, hqz⟩ := (hf x y).1 hxy
      obtain ⟨st, mid, h0, hst, hchain⟩ := A.mem_passes_iff_exists_chain.1 hq
      have hpass : ∀ j ≤ n + 1, st j ∈ A.passes (u x ++ v y) j := fun j hj =>
        A.mem_passes_iff_exists_chain.2 ⟨st, mid, h0, rfl, fun i hi => hchain i (by omega)⟩
      have hmid : ∀ j < n + 1, dec (enc (mid j)) = mid j := fun j hj =>
        A.decode_enc henc (A.mem_reachable_of_statesFrom (hm x y) hj (List.prefix_append _ _)
          (hpass j hj.le) (hchain j hj).1)
      have hst' : ∀ j < n, dec (enc (st (j + 1))) = st (j + 1) := fun j hj =>
        A.decode_enc henc (A.mem_reachable_of_passes (hm x y) (by omega) (hpass (j + 1) (by omega)))
      let w : (Fin (n + 1) → BitString b) × (Fin n → BitString b) :=
        (fun k => enc (mid k), fun k => enc (st (k + 1)))
      have hstart : ∀ j < n + 1, start A (n + 1) m b n enc w j = st j := by
        intro j hj
        rcases j with _ | j
        · rw [start_zero, h0]
        · rw [start_succ A _ _ _ _ _ _ (by omega : j < n)]
          exact hst' j (by omega)
      refine ⟨w, fun k => ?_, fun k => ?_, q, ?_, hqz⟩
      · change dec (enc (mid k)) ∈ _
        rw [hmid k k.2, hstart k k.2]
        exact (hchain k k.2).1
      · change dec (enc (st (k + 1))) ∈ A.pass (v y) (dec (enc (mid k)))
        rw [hst' k k.2, hmid k (by omega)]
        exact (hchain k (by omega)).2
      · change q ∈ A.pass (v y) (dec (enc (mid n)))
        rw [hmid n (by omega), ← hst]
        exact (hchain n (by omega)).2
  have hcard : Fintype.card ((Fin (n + 1) → BitString b) × (Fin n → BitString b)) =
      2 ^ ((2 * (n + 1) - 1) * b) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      ← pow_mul, ← pow_add]
    congr 1
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    ring
  refine ecomplexity_le_iff_coverNumber_le.2 (hC.coverNumber_le.trans ?_)
  rw [hcard]

end Algorithm

end Cslib.Streaming.Nondeterministic
