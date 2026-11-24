/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.EdgeNetBasic
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.TermBlocks
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.NetFamily

/-!
# The degree-3 network of a 3-CNF formula (Corollary 7.2)

A formula is given by *raw slot data* `Raw`: a number `m` of clauses and, for every slot
`t < 3m` (slot `j` of clause `t / 3` for `j = t % 3`), a slot value `sv t`: `0` for no literal and
`2 i + 1 + b` for the literal "`xᵢ = b`". This is the slot code `slot` of
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/ThreeSat/Decode.lean`.

Following the proof of Corollary 7.2 in the paper (a vertex at every clause and at every
occurrence of a variable, with the occurrences of each variable joined in a path by equalities),
the network `Raw.net` has `7m` vertices and `6m` edges:

* clause vertex `c < m`, with ports the occurrence edges `3c, 3c+1, 3c+2` of its slots; its
  function is the clause indicator (some present literal is satisfied, and the edges of empty
  slots carry `0`);
* occurrence vertex `m + t` of slot `t`, with ports the occurrence edge `t`, the chain edge
  `3m + t` and, if `t` has an earlier occurrence `prev t` of its variable, the chain edge
  `3m + prev t`; its function says that the occurrence edge equals the chain edges in use;
* sink vertex `4m + t`, which ends the chain edge `3m + t` when slot `t` has no later occurrence
  `next t` of its variable, forcing that unused edge to `0`.

The chain edge `3m + t` joins `m + t` to `m + next t` when `next t` exists and to the sink
`4m + t` otherwise. Every vertex has degree at most `3` and every function takes the values `0`
and `1`.

## Main definitions

* `Raw`, `Raw.next`, `Raw.prev`, `Raw.net`.
* `Raw.SatA`: an assignment of the variables `< N` satisfies every clause.

## Main results

* `Raw.value_net`: if every present slot names a variable `< N` and every variable `< N` occurs,
  then `Z(Raw.net) = #{a : Fin N → Bool | a satisfies every clause}`.
* `Raw.portsN_length_le`, `Raw.nodup_portsN`: degree at most `3` and duplicate-free ports.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat

open Finset NtimeDspace.Cross.TermBlocks

/-! ### The last index passing a test -/

/-- The last `i < k` with `p i`, or `d` if there is none. -/
def lastNat (d k : ℕ) (p : ℕ → Bool) : ℕ :=
  (List.range k).foldl (fun acc i => if p i then i else acc) d

theorem lastNat_succ (d k : ℕ) (p : ℕ → Bool) :
    lastNat d (k + 1) p = if p k then k else lastNat d k p := by
  simp [lastNat, List.range_succ, List.foldl_append]

theorem lastNat_spec (d k : ℕ) (p : ℕ → Bool) :
    (lastNat d k p = d ∧ ∀ i < k, p i = false) ∨
    (lastNat d k p < k ∧ p (lastNat d k p) = true ∧
      ∀ i, lastNat d k p < i → i < k → p i = false) := by
  induction k with
  | zero => left; simp [lastNat]
  | succ k ih =>
    rw [lastNat_succ]
    by_cases hk : p k = true
    · right
      rw [ite_eq_left hk]
      exact ⟨by omega, hk, fun i h1 h2 => by omega⟩
    · have hk' : p k = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ite_false]
      rcases ih with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · left
        refine ⟨h1, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact h2 i h
        · subst h; exact hk'
      · right
        refine ⟨by omega, h2, fun i hi1 hi2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi2 with h | h
        · exact h3 i hi1 h
        · subst h; exact hk'

/-! ### Raw slot data -/

/-- Raw slot data: `m` clauses and the slot values `sv t` (`0`: no literal; `2i+1+b`: `xᵢ = b`). -/
structure Raw where
  /-- The number of clauses. -/
  m : ℕ
  /-- The slot values. -/
  sv : ℕ → ℕ

namespace Raw

variable (d : Raw)

/-- Slot `t` holds a literal. -/
def pres (t : ℕ) : Bool := d.sv t != 0

/-- The variable of slot `t`. -/
def var (t : ℕ) : ℕ := (d.sv t - 1) / 2

/-- The value of the variable of slot `t` that satisfies its literal. -/
def sign (t : ℕ) : Bool := (d.sv t - 1) % 2 == 1

/-- Slot `t'` holds an occurrence of the variable of slot `t`. -/
def same (t t' : ℕ) : Bool := d.pres t' && d.var t' == d.var t

/-- The first later slot with the same variable, or `3m`. -/
def next (t : ℕ) : ℕ := firstNat (3 * d.m) (fun t' => decide (t < t') && d.same t t') (3 * d.m)

/-- Slot `t` holds a literal whose variable occurs again later. -/
def hasNext (t : ℕ) : Bool := d.pres t && decide (d.next t < 3 * d.m)

/-- The last earlier slot with the same variable, or `t`. -/
def prev (t : ℕ) : ℕ := lastNat t t (d.same t)

/-- Slot `t` holds a literal whose variable occurred before. -/
def hasPrev (t : ℕ) : Bool := d.pres t && decide (d.prev t < t)

variable {d}

theorem same_iff {t t' : ℕ} : d.same t t' = true ↔ d.pres t' = true ∧ d.var t' = d.var t := by
  simp [same]

theorem next_spec {t : ℕ} (h : d.hasNext t = true) :
    t < d.next t ∧ d.next t < 3 * d.m ∧ d.pres (d.next t) = true ∧ d.var (d.next t) = d.var t ∧
      ∀ t', t < t' → t' < d.next t → d.same t t' = false := by
  simp only [hasNext, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, hlt⟩ := h
  obtain ⟨h1, -, h3⟩ := firstNat_spec (3 * d.m) (fun t' => decide (t < t') && d.same t t')
      (3 * d.m) le_rfl
  obtain ⟨-, hp⟩ := h1 hlt
  simp only [Bool.and_eq_true, decide_eq_true_eq, same_iff] at hp
  refine ⟨hp.1, hlt, hp.2.1, hp.2.2, fun t' ht1 ht2 => ?_⟩
  have hc : t' < firstNat (3 * d.m) (fun t' => decide (t < t') && d.same t t') (3 * d.m) := ht2
  have := h3 t' (lt_min (ht2.trans hlt) hc)
  simpa [ht1] using this

theorem next_le {t t' : ℕ} (hp : d.pres t = true) (htt : t < t') (ht' : t' < 3 * d.m)
    (hs : d.same t t' = true) : d.hasNext t = true ∧ d.next t ≤ t' := by
  obtain ⟨h1, h2, h3⟩ := firstNat_spec (3 * d.m) (fun t' => decide (t < t') && d.same t t')
      (3 * d.m) le_rfl
  have hle : d.next t ≤ t' := by
    by_contra hc
    have hc' : t' < firstNat (3 * d.m) (fun t' => decide (t < t') && d.same t t') (3 * d.m) := by
      unfold next at hc; omega
    have := h3 t' (lt_min ht' hc')
    simp [htt, hs] at this
  exact ⟨by simp [hasNext, hp]; omega, hle⟩

theorem prev_spec {t : ℕ} (h : d.hasPrev t = true) :
    d.prev t < t ∧ d.same t (d.prev t) = true ∧ ∀ i, d.prev t < i → i < t → d.same t i = false := by
  simp only [hasPrev, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases lastNat_spec t t (d.same t) with ⟨h1, -⟩ | h'
  · exact absurd h.2 (by unfold prev; omega)
  · exact h'

theorem prev_ge {t t' : ℕ} (hp : d.pres t = true) (htt : t' < t) (hs : d.same t t' = true) :
    d.hasPrev t = true ∧ t' ≤ d.prev t := by
  rcases lastNat_spec t t (d.same t) with ⟨-, h2⟩ | ⟨h1, -, h3⟩
  · rw [h2 t' htt] at hs; exact absurd hs (by simp)
  · have hle : t' ≤ d.prev t := by
      by_contra hc
      have hc' : lastNat t t (d.same t) < t' := by unfold prev at hc; omega
      rw [h3 t' hc' htt] at hs
      exact absurd hs (by simp)
    exact ⟨by simp only [hasPrev, hp, Bool.true_and, decide_eq_true_eq]; exact h1, hle⟩

/-- The previous occurrence of the next occurrence is the slot itself. -/
theorem prev_next {t : ℕ} (h : d.hasNext t = true) :
    d.hasPrev (d.next t) = true ∧ d.prev (d.next t) = t := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := next_spec h
  have hpt : d.pres t = true := by simp only [hasNext, Bool.and_eq_true] at h; exact h.1
  have hs : d.same (d.next t) t = true := same_iff.mpr ⟨hpt, h4.symm⟩
  obtain ⟨hp, hle⟩ := prev_ge h3 h1 hs
  refine ⟨hp, le_antisymm ?_ hle⟩
  by_contra hc
  obtain ⟨hlt, hsame, -⟩ := prev_spec hp
  have := h5 (d.prev (d.next t)) (by omega) hlt
  rw [same_iff] at hsame
  rw [show d.same t (d.prev (d.next t)) = true from same_iff.mpr
      ⟨hsame.1, hsame.2.trans h4⟩] at this
  exact absurd this (by simp)

/-- The next occurrence of the previous occurrence is the slot itself. -/
theorem next_prev {t : ℕ} (h : d.hasPrev t = true) (ht : t < 3 * d.m) :
    d.hasNext (d.prev t) = true ∧ d.next (d.prev t) = t := by
  obtain ⟨h1, h2, h3⟩ := prev_spec h
  have hpt : d.pres t = true := by simp only [hasPrev, Bool.and_eq_true] at h; exact h.1
  rw [same_iff] at h2
  have hs : d.same (d.prev t) t = true := same_iff.mpr ⟨hpt, h2.2.symm⟩
  obtain ⟨hn, hle⟩ := next_le h2.1 h1 ht hs
  refine ⟨hn, le_antisymm hle ?_⟩
  by_contra hc
  obtain ⟨hlt, -, hp', hv', -⟩ := next_spec hn
  have := h3 (d.next (d.prev t)) hlt (by omega)
  rw [show d.same t (d.next (d.prev t)) = true from same_iff.mpr ⟨hp', hv'.trans h2.2⟩] at this
  exact absurd this (by simp)

theorem hasNext_pres {t : ℕ} (h : d.hasNext t = true) : d.pres t = true := by
  simp only [hasNext, Bool.and_eq_true] at h; exact h.1

theorem hasPrev_pres {t : ℕ} (h : d.hasPrev t = true) : d.pres t = true := by
  simp only [hasPrev, Bool.and_eq_true] at h; exact h.1

/-! ### The network, on numbers -/

variable (d)

/-- The row end of edge `i`. -/
def uN (i : ℕ) : ℕ := if i < 3 * d.m then i / 3 else d.m + (i - 3 * d.m)

/-- The column end of edge `i`. -/
def wN (i : ℕ) : ℕ :=
  if i < 3 * d.m then d.m + i
  else if d.hasNext (i - 3 * d.m) then d.m + d.next (i - 3 * d.m) else 4 * d.m + (i - 3 * d.m)

/-- The ports of vertex `v`, in order. -/
def portsN (v : ℕ) : List ℕ :=
  if v < d.m then [3 * v, 3 * v + 1, 3 * v + 2]
  else if v < 4 * d.m then
    [v - d.m, 3 * d.m + (v - d.m)] ++
      (if d.hasPrev (v - d.m) then [3 * d.m + d.prev (v - d.m)] else [])
  else if d.hasNext (v - 4 * d.m) then [] else [3 * d.m + (v - 4 * d.m)]

/-- The clause indicator of clause `c`, at the bits on its three occurrence edges. -/
def clauseOK (c : ℕ) (bs : List Bool) : Bool :=
  (List.range 3).all (fun j => d.pres (3 * c + j) || !(bs.getD j false)) &&
    (List.range 3).any (fun j => d.pres (3 * c + j) && (bs.getD j false == d.sign (3 * c + j)))

/-- The equality indicator of the occurrence vertex of slot `t`. -/
def occOK (t : ℕ) (bs : List Bool) : Bool :=
  (!d.hasNext t || bs.getD 0 false == bs.getD 1 false) &&
    (!d.hasPrev t || bs.getD 0 false == bs.getD 2 false)

/-- The indicator of the sink vertex of slot `t`: an unused chain edge carries `0`. -/
def sinkOK (t : ℕ) (bs : List Bool) : Bool := d.hasNext t || !(bs.getD 0 false)

/-- The function of vertex `v`, as a Boolean. -/
def evalN (v : ℕ) (bs : List Bool) : Bool :=
  if v < d.m then d.clauseOK v bs
  else if v < 4 * d.m then d.occOK (v - d.m) bs else d.sinkOK (v - 4 * d.m) bs

variable {d}

theorem uN_lt {i : ℕ} (hi : i < 6 * d.m) : d.uN i < 7 * d.m := by
  unfold uN; split_ifs <;> omega

theorem wN_lt {i : ℕ} (hi : i < 6 * d.m) : d.wN i < 7 * d.m := by
  unfold wN
  split_ifs with h1 h2
  · omega
  · have := (next_spec h2).2.1; omega
  · omega

theorem uN_ne_wN {i : ℕ} (hi : i < 6 * d.m) : d.uN i ≠ d.wN i := by
  unfold uN wN
  split_ifs with h1 h2
  · omega
  · have := (next_spec h2).1; omega
  · omega

theorem mem_portsN_lt {v i : ℕ} (hv : v < 7 * d.m) (h : i ∈ d.portsN v) : i < 6 * d.m := by
  unfold portsN at h
  split_ifs at h with h1 h2 h3 h4
  · simp at h; omega
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    have := (prev_spec h3).1; omega
  · simp at h; omega
  · simp at h
  · simp at h; omega

theorem portsN_length_le (v : ℕ) : (d.portsN v).length ≤ 3 := by
  unfold portsN; split_ifs <;> simp

theorem nodup_portsN {v : ℕ} (hv : v < 7 * d.m) : (d.portsN v).Nodup := by
  unfold portsN
  split_ifs with h1 h2 h3 h4
  · simp
  · have := (prev_spec h3).1
    simp; omega
  · simp; omega
  · simp
  · simp

/-- **Incidences.** Edge `i` is a port of `v` exactly when `v` is one of its ends. -/
theorem mem_portsN_iff {v i : ℕ} (_hv : v < 7 * d.m) (hi : i < 6 * d.m) :
    i ∈ d.portsN v ↔ d.uN i = v ∨ d.wN i = v := by
  unfold portsN uN wN
  by_cases hvm : v < d.m
  · simp only [hvm, ite_true, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h; left; rw [ite_eq_left (by omega)]; omega
    · rintro (h | h)
      · split_ifs at h with h1 <;> omega
      · split_ifs at h with h1 h2
        · omega
        · have := (next_spec h2).1; omega
        · omega
  · by_cases hv4 : v < 4 * d.m
    · simp only [hvm, hv4, ite_false, ite_true, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      constructor
      · rintro ((h | h) | h)
        · right; rw [ite_eq_left (by omega)]; omega
        · left; rw [ite_eq_right (by omega)]; omega
        · split_ifs at h with h3
          · simp only [List.mem_singleton] at h
            right
            have hvt : v - d.m < 3 * d.m := by omega
            obtain ⟨hn, hnext⟩ := next_prev h3 hvt
            have hp := (prev_spec h3).1
            rw [ite_eq_right (by omega), show i - 3 * d.m = d.prev (v - d.m) by omega,
                ite_eq_left hn, hnext]
            omega
          · simp at h
      · rintro (h | h)
        · split_ifs at h with h1
          · omega
          · left; right; omega
        · split_ifs at h with h1 h2
          · left; left; omega
          · right
            have hp := prev_next h2
            have hnt : d.next (i - 3 * d.m) = v - d.m := by omega
            rw [hnt] at hp
            rw [ite_eq_left hp.1, hp.2]
            simp only [List.mem_singleton]
            omega
          · omega
    · simp only [hvm, hv4, ite_false]
      constructor
      · intro h
        split_ifs at h with h4
        · simp at h
        · simp only [List.mem_singleton] at h
          right; rw [ite_eq_right (by omega), show i - 3 * d.m = v - 4 * d.m by omega,
              ite_eq_right h4]; omega
      · rintro (h | h)
        · split_ifs at h with h1 <;> omega
        · split_ifs at h with h1 h2
          · omega
          · have := (next_spec h2).2.1; omega
          · have ht : i - 3 * d.m = v - 4 * d.m := by omega
            rw [← ht, ite_eq_right h2]
            simp only [List.mem_singleton]
            omega

/-! ### The network as an `EdgeNet` -/

variable (d)

/-- **The network of the raw slot data**, with tables in `R`. -/
def net (R : Type) [Zero R] [One R] : EdgeNet R (Fin (7 * d.m)) where
  M := 6 * d.m
  u i := ⟨d.uN i, uN_lt i.2⟩
  w i := ⟨d.wN i, wN_lt i.2⟩
  huw i h := uN_ne_wN i.2 (congrArg Fin.val h)
  ports v := (d.portsN v).pmap (fun i h => ⟨i, h⟩) fun _ h => mem_portsN_lt v.2 h
  hports v i := by
    rw [List.mem_pmap]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases (mem_portsN_iff v.2 (mem_portsN_lt v.2 ha)).mp ha with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    · intro h
      refine ⟨i, (mem_portsN_iff v.2 i.2).mpr ?_, rfl⟩
      rcases h with h | h
      · left; exact congrArg Fin.val h
      · right; exact congrArg Fin.val h
  eval v bs := if d.evalN v bs then 1 else 0

variable {d}

@[simp] theorem net_M (R : Type) [Zero R] [One R] : (d.net R).M = 6 * d.m := rfl

theorem map_val_ports (R : Type) [Zero R] [One R] (v : Fin (7 * d.m)) :
    ((d.net R).ports v).map Fin.val = d.portsN v := by
  simp [net, List.map_pmap]

theorem net_u (R : Type) [Zero R] [One R] (i : Fin (d.net R).M) : ((d.net R).u i : ℕ) = d.uN i :=
    rfl
theorem net_w (R : Type) [Zero R] [One R] (i : Fin (d.net R).M) : ((d.net R).w i : ℕ) = d.wN i :=
    rfl
theorem net_eval (R : Type) [Zero R] [One R] (v : Fin (7 * d.m)) (bs : List Bool) :
    (d.net R).eval v bs = if d.evalN v bs then 1 else 0 := rfl

theorem nodup_net_ports (R : Type) [Zero R] [One R] (v : Fin (7 * d.m)) :
    ((d.net R).ports v).Nodup := by
  have h := nodup_portsN (d := d) v.2
  rw [← map_val_ports R v] at h
  exact h.of_map _

theorem net_degree_le (R : Type) [Zero R] [One R] (v : Fin (7 * d.m)) :
    ((d.net R).ports v).length ≤ 3 := by
  have h := portsN_length_le (d := d) v
  rw [← map_val_ports R v, List.length_map] at h
  exact h

/-! ### The value -/

/-- The edge bits as a function on numbers. -/
def ext (x : Fin (6 * d.m) → Bool) (e : ℕ) : Bool := if h : e < 6 * d.m then x ⟨e, h⟩ else false

/-- The constraints of all vertices, on edge bits `y`. -/
structure GoodN (d : Raw) (y : ℕ → Bool) : Prop where
  empty : ∀ t < 3 * d.m, d.pres t = false → y t = false
  clause : ∀ c < d.m, ∃ j < 3, d.pres (3 * c + j) = true ∧ y (3 * c + j) = d.sign (3 * c + j)
  nxt : ∀ t < 3 * d.m, d.hasNext t = true → y t = y (3 * d.m + t)
  prv : ∀ t < 3 * d.m, d.hasPrev t = true → y t = y (3 * d.m + d.prev t)
  sink : ∀ t < 3 * d.m, d.hasNext t = false → y (3 * d.m + t) = false

theorem getD_three (a b c : Bool) (j : ℕ) (hj : j < 3) (y : ℕ → Bool) (k : ℕ)
    (ha : a = y k) (hb : b = y (k + 1)) (hc : c = y (k + 2)) : [a, b, c].getD j false = y
        (k + j) := by
  interval_cases j <;> simp [ha, hb, hc]

/-- **The product of the vertex functions is the indicator of `GoodN`.** -/
theorem all_evalN_iff (y : ℕ → Bool) :
    (∀ v < 7 * d.m, d.evalN v ((d.portsN v).map y) = true) ↔ d.GoodN y := by
  constructor
  · intro h
    refine
        ⟨fun t ht hp => ?_, fun c hc => ?_, fun t ht hn => ?_, fun t ht hp => ?_, fun t ht hn => ?_⟩
    · have := h (t / 3) (by omega)
      simp only [evalN, portsN, show t / 3 < d.m by omega, ite_true, clauseOK, List.map_cons,
        List.map_nil, Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
      have h1 := this.1 (t % 3) (Nat.mod_lt _ (by norm_num))
      rw [show 3 * (t / 3) + t % 3 = t by omega, hp, Bool.false_or, Bool.not_eq_true'] at h1
      rw [getD_three _ _ _ _ (Nat.mod_lt _ (by norm_num)) y (3 * (t / 3)) rfl rfl rfl,
        show 3 * (t / 3) + t % 3 = t by omega] at h1
      exact h1
    · have := h c (by omega)
      simp only [evalN, portsN, hc, ite_true, clauseOK, List.map_cons, List.map_nil,
          Bool.and_eq_true,
        List.any_eq_true, List.mem_range, beq_iff_eq] at this
      obtain ⟨j, hj, hp, hs⟩ := this.2
      exact ⟨j, hj, hp, by rw [← hs, getD_three _ _ _ _ hj y (3 * c) rfl rfl rfl]⟩
    · have := h (d.m + t) (by omega)
      simp only [evalN, portsN, show ¬ d.m + t < d.m by omega, show d.m + t < 4 * d.m by omega,
        ite_true, ite_false, Nat.add_sub_cancel_left, occOK, hn, Bool.not_true, Bool.false_or,
        Bool.and_eq_true, beq_iff_eq] at this
      simpa using this.1
    · have := h (d.m + t) (by omega)
      simp only [evalN, portsN, show ¬ d.m + t < d.m by omega, show d.m + t < 4 * d.m by omega,
        ite_true, ite_false, Nat.add_sub_cancel_left, occOK, hp, Bool.not_true, Bool.false_or,
        Bool.and_eq_true, beq_iff_eq] at this
      simpa using this.2
    · have := h (4 * d.m + t) (by omega)
      simp only [evalN, portsN, show ¬ 4 * d.m + t < d.m by omega,
        show ¬ 4 * d.m + t < 4 * d.m by omega, ite_false, Nat.add_sub_cancel_left, sinkOK, hn,
        Bool.false_or, Bool.false_eq_true] at this
      simpa using this
  · intro hg v hv
    by_cases h1 : v < d.m
    · simp only [evalN, portsN, h1, ite_true, clauseOK, List.map_cons, List.map_nil,
        Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq,
        Bool.or_eq_true, Bool.not_eq_true']
      refine ⟨fun j hj => ?_, ?_⟩
      · rw [getD_three _ _ _ _ hj y (3 * v) rfl rfl rfl]
        by_cases hp : d.pres (3 * v + j) = true
        · exact Or.inl hp
        · exact Or.inr (hg.empty _ (by omega) (by simpa using hp))
      · obtain ⟨j, hj, hp, hs⟩ := hg.clause v h1
        exact ⟨j, hj, hp, by rw [getD_three _ _ _ _ hj y (3 * v) rfl rfl rfl, hs]⟩
    · by_cases h4 : v < 4 * d.m
      · simp only [evalN, portsN, h1, h4, ite_true, ite_false, occOK, Bool.and_eq_true,
          Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
        refine ⟨?_, ?_⟩
        · by_cases hn : d.hasNext (v - d.m) = true
          · right; simpa using hg.nxt _ (by omega) hn
          · left; simpa using hn
        · by_cases hp : d.hasPrev (v - d.m) = true
          · right; simpa [hp] using hg.prv _ (by omega) hp
          · left; simpa using hp
      · simp only [evalN, portsN, h1, h4, ite_false, sinkOK, Bool.or_eq_true, Bool.not_eq_true']
        by_cases hn : d.hasNext (v - 4 * d.m) = true
        · exact Or.inl hn
        · right
          have hn' : d.hasNext (v - 4 * d.m) = false := by simpa using hn
          simpa [hn'] using hg.sink _ (by omega) hn'

/-- The first slot holding variable `k`, or `3m`. -/
def firstOcc (d : Raw) (k : ℕ) : ℕ := firstNat (3 * d.m)
    (fun t => d.pres t && d.var t == k) (3 * d.m)

/-- An assignment of the variables `< N`, as a function on numbers. -/
def extA {N : ℕ} (a : Fin N → Bool) (k : ℕ) : Bool := if h : k < N then a ⟨k, h⟩ else false

/-- `a` satisfies every clause. -/
def SatA (d : Raw) {N : ℕ} (a : Fin N → Bool) : Prop :=
  ∀ c < d.m, ∃ j < 3, d.pres (3 * c + j) = true ∧ extA a (d.var (3 * c + j)) = d.sign (3 * c + j)

instance {N : ℕ} (a : Fin N → Bool) : Decidable (d.SatA a) := by unfold SatA; infer_instance

/-- **Chains.** Under the vertex constraints, all occurrences of a variable carry the same bit. -/
theorem GoodN.chain {y : ℕ → Bool} (hg : d.GoodN y) {t t' : ℕ} (ht' : t' < 3 * d.m)
    (hp : d.pres t = true) (hp' : d.pres t' = true) (hv : d.var t = d.var t') (htt : t < t') :
    y t = y t' := by
  induction h : t' - t using Nat.strong_induction_on generalizing t with
  | _ k ih =>
    obtain ⟨hn, hle⟩ := next_le hp htt ht' (same_iff.mpr ⟨hp', hv.symm⟩)
    obtain ⟨h1, h2, h3, h4, -⟩ := next_spec hn
    obtain ⟨hp2, hprev⟩ := prev_next hn
    have e1 : y t = y (d.next t) := by
      have a1 := hg.nxt t (by omega) hn
      have a2 := hg.prv _ h2 hp2
      rw [hprev] at a2
      exact a1.trans a2.symm
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · rw [e1]; exact ih (t' - d.next t) (by omega) h3 (h4.trans hv) hlt rfl
    · rw [e1, heq]

theorem GoodN.chain' {y : ℕ → Bool} (hg : d.GoodN y) {t t' : ℕ} (ht : t < 3 * d.m)
    (ht' : t' < 3 * d.m) (hp : d.pres t = true) (hp' : d.pres t' = true) (hv : d.var t = d.var t') :
    y t = y t' := by
  rcases lt_trichotomy t t' with h | rfl | h
  · exact hg.chain ht' hp hp' hv h
  · rfl
  · exact (hg.chain ht hp' hp hv.symm h).symm

theorem firstOcc_spec {k : ℕ} (h : ∃ t < 3 * d.m, d.pres t = true ∧ d.var t = k) :
    d.firstOcc k < 3 * d.m ∧ d.pres (d.firstOcc k) = true ∧ d.var (d.firstOcc k) = k := by
  obtain ⟨t, ht, hp, hv⟩ := h
  obtain ⟨h1, h2, h3⟩ := firstNat_spec (3 * d.m) (fun t => d.pres t && d.var t == k)
      (3 * d.m) le_rfl
  rcases h2 with h2 | h2
  · have := h3 t (by omega)
    simp [hp, hv] at this
  · obtain ⟨-, hq⟩ := h1 h2
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    exact ⟨h2, hq⟩

/-- **The value of the network.** If every present slot names a variable `< N` and every variable
`< N` occurs, then `Z` is the number of assignments of the variables `< N` satisfying every
clause. -/
theorem value_net (R : Type) [CommRing R] (N : ℕ)
    (hvar : ∀ t < 3 * d.m, d.pres t = true → d.var t < N)
    (hocc : ∀ k < N, ∃ t < 3 * d.m, d.pres t = true ∧ d.var t = k) :
    (d.net R).value = ((univ.filter fun a : Fin N → Bool => d.SatA a).card : R) := by
  classical
  -- the product of the vertex functions
  have hprod : ∀ x : Fin (6 * d.m) → Bool,
      ∏ v, (d.net R).eval v (((d.net R).ports v).map x) = if d.GoodN (ext x) then 1 else 0 := by
    intro x
    have hmap : ∀ v : Fin (7 * d.m), ((d.net R).ports v).map x = (d.portsN v).map (ext x) := by
      intro v
      rw [← map_val_ports R v, List.map_map]
      refine List.map_congr_left fun i _ => ?_
      simp [ext, i.2]
    simp only [hmap, net_eval]
    rw
        [Fin.prod_univ_eq_prod_range
        (fun v => if d.evalN v ((d.portsN v).map (ext x)) = true then (1 : R) else 0),
      prod_boole]
    congr 1
    refine propext ⟨fun h => (all_evalN_iff (ext x)).mp fun v hv => h v (mem_range.mpr hv),
      fun h v hv => (all_evalN_iff (ext x)).mpr h v (mem_range.mp hv)⟩
  rw [EdgeNet.value]
  simp only [net_M] at hprod ⊢
  rw [Finset.sum_congr rfl fun x _ => hprod x, sum_boole]
  congr 1
  -- the bijection between consistent edge bits and satisfying assignments
  refine Finset.card_bij' (fun x _ => fun k : Fin N => ext x (d.firstOcc k))
    (fun a _ => fun e : Fin (6 * d.m) => if (e : ℕ) < 3 * d.m then d.pres e && extA a (d.var e)
      else d.hasNext (e - 3 * d.m) && extA a (d.var (e - 3 * d.m))) ?_ ?_ ?_ ?_
  · -- consistent edge bits give a satisfying assignment
    intro x hx
    rw [mem_filter] at hx ⊢
    replace hx := hx.2
    refine ⟨mem_univ _, fun c hc => ?_⟩
    obtain ⟨j, hj, hp, hs⟩ := hx.clause c hc
    refine ⟨j, hj, hp, ?_⟩
    have hvN := hvar _ (by omega) hp
    obtain ⟨f1, f2, f3⟩ := firstOcc_spec (hocc _ hvN)
    simp only [extA, dite_eq_left hvN]
    rw [hx.chain' f1 (by omega) f2 hp f3, hs]
  · -- satisfying assignments give consistent edge bits
    intro a ha
    rw [mem_filter] at ha ⊢
    replace ha := ha.2
    refine ⟨mem_univ _, ?_⟩
    have hext : ∀ e < 6 * d.m, ext (fun e : Fin (6 * d.m) => if (e : ℕ) < 3 * d.m then
        d.pres e && extA a (d.var e) else d.hasNext (e - 3 * d.m) && extA a
            (d.var (e - 3 * d.m))) e =
        if e < 3 * d.m then d.pres e && extA a (d.var e)
        else d.hasNext (e - 3 * d.m) && extA a (d.var (e - 3 * d.m)) := fun e he => by
      simp [ext, he]
    refine
        ⟨fun t ht hp => ?_, fun c hc => ?_, fun t ht hn => ?_, fun t ht hp => ?_, fun t ht hn => ?_⟩
    · rw [hext t (by omega), ite_eq_left ht, hp, Bool.false_and]
    · obtain ⟨j, hj, hp, hs⟩ := ha c hc
      exact ⟨j, hj, hp, by rw [hext _ (by omega), ite_eq_left (by omega), hp, Bool.true_and, hs]⟩
    · rw [hext t (by omega), hext (3 * d.m + t) (by omega), ite_eq_left ht, ite_eq_right (by omega),
        Nat.add_sub_cancel_left, hn, hasNext_pres hn]
    · obtain ⟨h1, h2, -⟩ := prev_spec hp
      obtain ⟨hn, -⟩ := next_prev hp ht
      rw [same_iff] at h2
      rw [hext t (by omega), hext (3 * d.m + d.prev t) (by omega), ite_eq_left ht,
          ite_eq_right (by omega),
        Nat.add_sub_cancel_left, hn, hasPrev_pres hp, h2.2]
    · rw [hext (3 * d.m + t) (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left, hn,
        Bool.false_and]
  · -- left inverse
    intro x hx
    rw [mem_filter] at hx
    replace hx := hx.2
    funext e
    have he := e.2
    by_cases h3 : (e : ℕ) < 3 * d.m
    · rw [ite_eq_left h3]
      by_cases hp : d.pres e = true
      · have hvN := hvar _ h3 hp
        obtain ⟨f1, f2, f3⟩ := firstOcc_spec (hocc _ hvN)
        simp only [hp, Bool.true_and, extA, dite_eq_left hvN]
        rw [hx.chain' f1 h3 f2 hp f3]
        simp [ext]
      · have hp' : d.pres e = false := by simpa using hp
        rw [hp', Bool.false_and]
        have := hx.empty e h3 hp'
        simp only [ext, dite_eq_left he] at this
        exact this.symm
    · rw [ite_eq_right h3]
      have ht : (e : ℕ) - 3 * d.m < 3 * d.m := by omega
      have hee : 3 * d.m + ((e : ℕ) - 3 * d.m) = e := by omega
      by_cases hn : d.hasNext (e - 3 * d.m) = true
      · have hp := hasNext_pres hn
        have hvN := hvar _ ht hp
        obtain ⟨f1, f2, f3⟩ := firstOcc_spec (hocc _ hvN)
        simp only [hn, Bool.true_and, extA, dite_eq_left hvN]
        rw [hx.chain' f1 ht f2 hp f3, hx.nxt _ ht hn, hee]
        simp [ext]
      · have hn' : d.hasNext (e - 3 * d.m) = false := by simpa using hn
        rw [hn', Bool.false_and]
        have := hx.sink _ ht hn'
        rw [hee] at this
        simp only [ext, dite_eq_left he] at this
        exact this.symm
  · -- right inverse
    intro a _
    funext k
    obtain ⟨f1, f2, f3⟩ := firstOcc_spec (hocc k k.2)
    simp only [ext, dite_eq_left (show d.firstOcc k < 6 * d.m by omega), ite_eq_left f1,
        f2, Bool.true_and,
        f3,
      extA, dite_eq_left k.2]

end Raw

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat
