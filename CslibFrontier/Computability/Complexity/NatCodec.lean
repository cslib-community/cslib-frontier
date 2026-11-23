/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import Mathlib.Data.Nat.Pairing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryPair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Composable natural-number index codecs for hardness reductions

Many polynomial-time and parsimonious reductions allocate fresh natural-number variable or vertex
names across several disjoint roles — original vertices or variables, fixed hub/pendant gadgets,
clause-splitting pairs, occurrence-splitting triples, or layered arc gadgets — and then discharge
injectivity, non-collision between roles, partial decoding, binary bit-length bounds, and
`ComputableInPolyTime` certificates under `Turing.MultiTapeTM.encNat`.

`Cslib.Complexity.NatCodec α` packages a computable numbering `encode : α → ℕ` together with its
exact partial inverse `decode? : ℕ → Option α` (`decode? n = some a ↔ encode a = n`). Combinators
build compound namespaces without ad-hoc parity or `Nat.unpair` arithmetic:

* `NatCodec.nat`, `NatCodec.fin`: base codecs for `ℕ` and `Fin k`.
* `NatCodec.shift`, `NatCodec.finSum`: offset a namespace by `k`, or reserve `0, …, k - 1` for
  `Fin k` while shifting a payload namespace above `k`.
* `NatCodec.sum`: interleave two namespaces at even (`2 * c₁ a`) and odd (`2 * c₂ b + 1`) indices,
  with automatic range disjointness (`disjoint_range_sum`).
* `NatCodec.pair`: combine two namespaces through Cantor-style pairing `Nat.pair`, doubling
  worst-case binary bit-length (`Nat.size_pair_le`, `NatCodec.size_pair_le`).

All combinators carry `@[fun_prop]` `ComputableInPolyTime` rules into `encNat`, using
`Turing.MultiTapeTM.ComputableInPolyTime.sumElim` from `PolyTime.Sum`.

## Main definitions

* `Cslib.Complexity.NatCodec`: computable natural-number codec with exact partial inverse
  `decode?` and embedding coercion `NatCodec.toEmbedding`.
* `Cslib.Complexity.NatCodec.nat`, `Cslib.Complexity.NatCodec.fin`: base codecs.
* `Cslib.Complexity.NatCodec.shift`, `Cslib.Complexity.NatCodec.finSum`,
  `Cslib.Complexity.NatCodec.sum`, `Cslib.Complexity.NatCodec.pair`: offset, finite-prefix sum,
  even/odd sum, and `Nat.pair` product combinators.

## Main results

* `Cslib.Complexity.NatCodec.injective`, `Cslib.Complexity.NatCodec.decode?_eq_some_iff`,
  `Cslib.Complexity.NatCodec.decode?_eq_none_iff`: injectivity and exact range characterization of
  `decode?`.
* `Cslib.Complexity.NatCodec.disjoint_range_finSum`,
  `Cslib.Complexity.NatCodec.disjoint_range_sum`: automatic non-collision between summands.
* `Nat.size_pair_le`, `Cslib.Complexity.NatCodec.size_finSum_le`,
  `Cslib.Complexity.NatCodec.size_sum_le`, `Cslib.Complexity.NatCodec.size_pair_le`: binary
  bit-length bounds (`Nat.size` and `(encNat ·).length`).
* `Cslib.Complexity.NatCodec.computableInPolyTime_finSum`,
  `Cslib.Complexity.NatCodec.computableInPolyTime_sum`,
  `Cslib.Complexity.NatCodec.computableInPolyTime_pair`: `@[fun_prop]` polynomial-time certificates
  under `encNat` (including `encUnary` leaves via `computableInPolyTime_nat_unary`).
-/

public section

/-! ### Sharp binary bit-length bound for `Nat.pair` -/

namespace Nat

/-- Pairing two natural numbers of binary length at most `m` uses at most `2 m` binary digits. -/
theorem size_pair_le (a b : ℕ) : (Nat.pair a b).size ≤ 2 * max a.size b.size := by
  set m := max a.size b.size
  have ha : a + 1 ≤ 2 ^ m :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right two_pos (le_max_left _ _))
  have hb : b + 1 ≤ 2 ^ m :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right two_pos (le_max_right _ _))
  refine Nat.size_le.2 ?_
  rw [Nat.two_mul, Nat.pow_add, Nat.pair]
  split
  · exact lt_of_lt_of_le (show b * b + a < (b + 1) * (b + 1) by nlinarith) (Nat.mul_le_mul hb hb)
  · exact lt_of_lt_of_le (show a * a + a + b < (a + 1) * (a + 1) by nlinarith)
      (Nat.mul_le_mul ha ha)

end Nat

/-! ### `NatCodec` and its combinators -/

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- A computable injective numbering `encode : α → ℕ` equipped with its exact partial inverse
`decode? : ℕ → Option α` (`decode? n = some a ↔ encode a = n`). -/
structure NatCodec (α : Type*) where
  /-- Assign a natural-number index to `a`. -/
  encode : α → ℕ
  /-- Recover the unique `a` with `encode a = n`, or `none` outside the range of `encode`. -/
  decode? : ℕ → Option α
  /-- Encoding followed by `decode?` recovers the input. -/
  decode?_encode : ∀ a, decode? (encode a) = some a
  /-- Any `some a` returned by `decode? n` encodes back to `n`. -/
  encode_of_decode? : ∀ {n a}, decode? n = some a → encode a = n

namespace NatCodec

section Core

variable {α β : Type*}

instance : CoeFun (NatCodec α) (fun _ => α → ℕ) :=
  ⟨NatCodec.encode⟩

@[simp]
theorem decode?_apply (c : NatCodec α) (a : α) : c.decode? (c a) = some a :=
  c.decode?_encode a

/-- Every `NatCodec` is injective. -/
theorem injective (c : NatCodec α) : Function.Injective c :=
  fun a b h => Option.some.inj <| (c.decode?_apply a).symm.trans (h ▸ c.decode?_apply b)

@[simp]
theorem apply_eq_iff (c : NatCodec α) {a b : α} : c a = c b ↔ a = b :=
  c.injective.eq_iff

/-- View a `NatCodec` as an embedding `α ↪ ℕ`. -/
@[expose]
def toEmbedding (c : NatCodec α) : α ↪ ℕ :=
  ⟨c, c.injective⟩

/-- `c.decode? n` returns `some a` if and only if `c a = n`. -/
theorem decode?_eq_some_iff (c : NatCodec α) {n : ℕ} {a : α} :
    c.decode? n = some a ↔ c a = n :=
  ⟨c.encode_of_decode?, fun h => h ▸ c.decode?_apply a⟩

/-- `c.decode? n` succeeds if and only if `n` lies in `Set.range c`. -/
theorem isSome_decode?_iff (c : NatCodec α) {n : ℕ} :
    (c.decode? n).isSome ↔ n ∈ Set.range c := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun _ => c.decode?_eq_some_iff

/-- `c.decode? n` returns `none` if and only if `n` lies outside `Set.range c`. -/
theorem decode?_eq_none_iff (c : NatCodec α) {n : ℕ} :
    c.decode? n = none ↔ n ∉ Set.range c := by
  rw [← Option.not_isSome_iff_eq_none, c.isSome_decode?_iff]

/-- Binary word length of `c a` under `encNat` equals `(c a).size`. -/
theorem length_encNat (c : NatCodec α) (a : α) : (encNat (c a)).length = (c a).size :=
  Nat.size_eq_bits_len (c a)

end Core

/-! ### Base codecs and combinators -/

/-- Identity codec on `ℕ`. -/
@[expose]
def nat : NatCodec ℕ where
  encode n := n
  decode? := some
  decode?_encode _ := rfl
  encode_of_decode? h := (Option.some.inj h).symm

@[simp]
theorem nat_apply (n : ℕ) : nat n = n :=
  rfl

/-- Canonical codec for `Fin k` onto `{0, …, k - 1}`. -/
@[expose]
def fin (k : ℕ) : NatCodec (Fin k) where
  encode i := i.val
  decode? n := if h : n < k then some ⟨n, h⟩ else none
  decode?_encode i := by simp [i.isLt]
  encode_of_decode? {n _} h := by
    split at h
    · exact congrArg Fin.val (Option.some.inj h).symm
    · cases h

@[simp]
theorem fin_apply (k : ℕ) (i : Fin k) : fin k i = i.val :=
  rfl

theorem fin_lt (k : ℕ) (i : Fin k) : fin k i < k :=
  i.isLt

/-- Shift every index of `c` upward by `k`. -/
@[expose]
def shift {α : Type*} (k : ℕ) (c : NatCodec α) : NatCodec α where
  encode a := c.encode a + k
  decode? n := if k ≤ n then c.decode? (n - k) else none
  decode?_encode a := by
    simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]
    exact c.decode?_encode a
  encode_of_decode? {n a} h := by
    split at h
    · have ha := c.encode_of_decode? h
      omega
    · cases h

@[simp]
theorem shift_apply {α : Type*} (k : ℕ) (c : NatCodec α) (a : α) : c.shift k a = c a + k :=
  rfl

theorem le_shift {α : Type*} (k : ℕ) (c : NatCodec α) (a : α) : k ≤ c.shift k a :=
  Nat.le_add_left k (c a)

/-- Reserve `{0, …, k - 1}` for `Fin k` and shift `c` to `{k, k + 1, …}`. -/
@[expose]
def finSum {β : Type*} (k : ℕ) (c : NatCodec β) : NatCodec (Fin k ⊕ β) where
  encode := Sum.elim (fin k) (c.shift k)
  decode? n := if h : n < k then some (.inl ⟨n, h⟩) else ((c.shift k).decode? n).map .inr
  decode?_encode
    | .inl i => by simp [i.isLt]
    | .inr b => by
      have hlt : ¬c b + k < k := Nat.not_lt.mpr (le_shift k c b)
      simp only [Sum.elim_inr, shift_apply, hlt, ↓reduceDIte, Option.map_eq_some_iff]
      exact ⟨b, (c.shift k).decode?_encode b, rfl⟩
  encode_of_decode? {n x} h := by
    split at h
    · obtain rfl := Option.some.inj h
      rfl
    · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      exact (c.shift k).encode_of_decode? hb

@[simp]
theorem finSum_inl {β : Type*} (k : ℕ) (c : NatCodec β) (i : Fin k) :
    c.finSum k (.inl i) = i.val :=
  rfl

@[simp]
theorem finSum_inr {β : Type*} (k : ℕ) (c : NatCodec β) (b : β) :
    c.finSum k (.inr b) = c b + k :=
  rfl

theorem finSum_inl_ne_inr {β : Type*} (k : ℕ) (c : NatCodec β) (i : Fin k) (b : β) :
    c.finSum k (.inl i) ≠ c.finSum k (.inr b) :=
  (c.finSum k).injective.ne Sum.inl_ne_inr

theorem finSum_inr_ne_inl {β : Type*} (k : ℕ) (c : NatCodec β) (b : β) (i : Fin k) :
    c.finSum k (.inr b) ≠ c.finSum k (.inl i) :=
  (c.finSum k).injective.ne Sum.inr_ne_inl

/-- Left and right summands of `finSum` occupy disjoint subsets of `ℕ`. -/
theorem disjoint_range_finSum {β : Type*} (k : ℕ) (c : NatCodec β) :
    Disjoint (Set.range fun i => c.finSum k (.inl i))
      (Set.range fun b => c.finSum k (.inr b)) :=
  Set.disjoint_left.mpr fun _ ⟨i, hi⟩ ⟨b, hb⟩ => finSum_inl_ne_inr k c i b (hi.trans hb.symm)

/-- Interleave `c₁` on even indices (`2 * c₁ a`) and `c₂` on odd indices (`2 * c₂ b + 1`). -/
@[expose]
def sum {α β : Type*} (c₁ : NatCodec α) (c₂ : NatCodec β) : NatCodec (α ⊕ β) where
  encode := Sum.elim (fun a => 2 * c₁.encode a) (fun b => 2 * c₂.encode b + 1)
  decode? n :=
    if n % 2 = 0 then (c₁.decode? (n / 2)).map .inl else (c₂.decode? (n / 2)).map .inr
  decode?_encode
    | .inl a => by
      simp [Nat.mul_mod_right, Nat.mul_div_right _ two_pos, c₁.decode?_encode a]
    | .inr b => by
      have hmod : (2 * c₂.encode b + 1) % 2 = 1 := by omega
      have hdiv : (2 * c₂.encode b + 1) / 2 = c₂.encode b := by omega
      simp [hmod, hdiv, c₂.decode?_encode b]
  encode_of_decode? {n x} h := by
    split at h
    · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      have hca := c₁.encode_of_decode? ha
      simp only [Sum.elim_inl]
      omega
    · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      have hcb := c₂.encode_of_decode? hb
      simp only [Sum.elim_inr]
      omega

@[simp]
theorem sum_inl {α β : Type*} (c₁ : NatCodec α) (c₂ : NatCodec β) (a : α) :
    c₁.sum c₂ (.inl a) = 2 * c₁ a :=
  rfl

@[simp]
theorem sum_inr {α β : Type*} (c₁ : NatCodec α) (c₂ : NatCodec β) (b : β) :
    c₁.sum c₂ (.inr b) = 2 * c₂ b + 1 :=
  rfl

theorem sum_inl_ne_inr {α β : Type*} (c₁ : NatCodec α) (c₂ : NatCodec β) (a : α) (b : β) :
    c₁.sum c₂ (.inl a) ≠ c₁.sum c₂ (.inr b) :=
  (c₁.sum c₂).injective.ne Sum.inl_ne_inr

theorem sum_inr_ne_inl {α β : Type*} (c₁ : NatCodec α) (c₂ : NatCodec β) (b : β) (a : α) :
    c₁.sum c₂ (.inr b) ≠ c₁.sum c₂ (.inl a) :=
  (c₁.sum c₂).injective.ne Sum.inr_ne_inl

/-- Even and odd branches of `NatCodec.sum` occupy disjoint subsets of `ℕ`. -/
theorem disjoint_range_sum {α β : Type*} (c₁ : NatCodec α) (c₂ : NatCodec β) :
    Disjoint (Set.range fun a => c₁.sum c₂ (.inl a))
      (Set.range fun b => c₁.sum c₂ (.inr b)) :=
  Set.disjoint_left.mpr fun _ ⟨a, ha⟩ ⟨b, hb⟩ => sum_inl_ne_inr c₁ c₂ a b (ha.trans hb.symm)

/-- Product codec combining `c₁` and `c₂` through `Nat.pair` / `Nat.unpair`. -/
@[expose]
def pair {α β : Type*} (c₁ : NatCodec α) (c₂ : NatCodec β) : NatCodec (α × β) where
  encode p := Nat.pair (c₁.encode p.1) (c₂.encode p.2)
  decode? n :=
    let q := Nat.unpair n
    match c₁.decode? q.1, c₂.decode? q.2 with
    | some a, some b => some (a, b)
    | _, _ => none
  decode?_encode p := by
    change (match c₁.decode? (Nat.unpair (Nat.pair (c₁ p.1) (c₂ p.2))).1,
        c₂.decode? (Nat.unpair (Nat.pair (c₁ p.1) (c₂ p.2))).2 with
      | some a, some b => some (a, b) | _, _ => none) = some p
    rw [Nat.unpair_pair, c₁.decode?_apply, c₂.decode?_apply]
  encode_of_decode? {n p} h := by
    dsimp only at h
    cases h₁ : c₁.decode? (Nat.unpair n).1 <;>
      cases h₂ : c₂.decode? (Nat.unpair n).2 <;>
      simp only [h₁, h₂, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [c₁.encode_of_decode? h₁, c₂.encode_of_decode? h₂, Nat.pair_unpair]

@[simp]
theorem pair_apply {α β : Type*} (c₁ : NatCodec α) (c₂ : NatCodec β) (p : α × β) :
    c₁.pair c₂ p = Nat.pair (c₁ p.1) (c₂ p.2) :=
  rfl

/-! ### Binary bit-length bounds -/

section SizeBounds

variable {α β : Type*}

theorem size_fin_le (k : ℕ) (i : Fin k) : (fin k i).size ≤ k.size :=
  Nat.size_le_size i.isLt.le

theorem size_shift_le (k : ℕ) (c : NatCodec α) (a : α) :
    (c.shift k a).size ≤ max (c a).size k.size + 1 :=
  Nat.size_add_le_max (c a) k

/-- Prefixing `Fin k` and shifting `c` by `k` bounds binary bit-length by `k.size` on `.inl` and
`max (c b).size k.size + 1` on `.inr`. -/
theorem size_finSum_le (k : ℕ) (c : NatCodec β) (x : Fin k ⊕ β) :
    (c.finSum k x).size ≤ Sum.elim (fun _ => k.size) (fun b => max (c b).size k.size + 1) x := by
  cases x with
  | inl i => exact size_fin_le k i
  | inr b => exact size_shift_le k c b

theorem size_sum_inl_le (c₁ : NatCodec α) (c₂ : NatCodec β) (a : α) :
    (c₁.sum c₂ (.inl a)).size ≤ (c₁ a).size + 1 := by
  refine Nat.size_le.2 ?_
  rw [sum_inl, Nat.pow_succ']
  exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self (c₁ a)) two_pos

theorem size_sum_inr_eq (c₁ : NatCodec α) (c₂ : NatCodec β) (b : β) :
    (c₁.sum c₂ (.inr b)).size = (c₂ b).size + 1 := by
  rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len, sum_inr, Nat.bit1_bits, List.length_cons]

/-- Interleaving via `NatCodec.sum` adds at most one binary digit to the payload index. -/
theorem size_sum_le (c₁ : NatCodec α) (c₂ : NatCodec β) (x : α ⊕ β) :
    (c₁.sum c₂ x).size ≤ Sum.elim (fun a => (c₁ a).size) (fun b => (c₂ b).size) x + 1 := by
  cases x with
  | inl a => exact size_sum_inl_le c₁ c₂ a
  | inr b => exact (size_sum_inr_eq c₁ c₂ b).le

/-- Pairing via `NatCodec.pair` uses at most twice the larger payload bit-length. -/
theorem size_pair_le (c₁ : NatCodec α) (c₂ : NatCodec β) (p : α × β) :
    (c₁.pair c₂ p).size ≤ 2 * max (c₁ p.1).size (c₂ p.2).size :=
  Nat.size_pair_le (c₁ p.1) (c₂ p.2)

end SizeBounds

/-! ### Polynomial-time computability under `encNat` -/

section PolyTime

@[fun_prop]
theorem computableInPolyTime_nat : ComputableInPolyTime (fun n => nat n) encNat encNat :=
  .id'

/-- Unary natural indices convert to binary `encNat` indices in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_nat_unary : ComputableInPolyTime (fun n => nat n) encUnary encNat :=
  unary_to_binary

@[fun_prop]
theorem computableInPolyTime_fin (k : ℕ) {enc : Fin k ↪ List Bool} :
    ComputableInPolyTime (fun i => fin k i) enc encNat :=
  of_finite _

@[fun_prop]
theorem computableInPolyTime_shift {α : Type} {encA : α ↪ List Bool} {c : NatCodec α} (k : ℕ)
    (hc : ComputableInPolyTime (fun a => c a) encA encNat) :
    ComputableInPolyTime (fun a => c.shift k a) encA encNat :=
  binary_add' hc (const k)

@[fun_prop]
theorem computableInPolyTime_finSum {β : Type} {k : ℕ} {encF : Fin k ↪ List Bool}
    {encB : β ↪ List Bool} {c : NatCodec β}
    (hc : ComputableInPolyTime (fun b => c b) encB encNat) :
    ComputableInPolyTime (fun x => c.finSum k x) (encSum encF encB) encNat :=
  sumElim (computableInPolyTime_fin k) (computableInPolyTime_shift k hc)

@[fun_prop]
theorem computableInPolyTime_sum {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {c₁ : NatCodec α} {c₂ : NatCodec β}
    (hc₁ : ComputableInPolyTime (fun a => c₁ a) encA encNat)
    (hc₂ : ComputableInPolyTime (fun b => c₂ b) encB encNat) :
    ComputableInPolyTime (fun x => c₁.sum c₂ x) (encSum encA encB) encNat :=
  sumElim (binary_mul' (const 2) hc₁) (binary_add' (binary_mul' (const 2) hc₂) (const 1))

@[fun_prop]
theorem computableInPolyTime_pair {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {c₁ : NatCodec α} {c₂ : NatCodec β}
    (hc₁ : ComputableInPolyTime (fun a => c₁ a) encA encNat)
    (hc₂ : ComputableInPolyTime (fun b => c₂ b) encB encNat) :
    ComputableInPolyTime (fun p => c₁.pair c₂ p) (encPair encA encB) encNat :=
  binary_pair' (hc₁.comp (fst encA encB)) (hc₂.comp (snd encA encB))

end PolyTime

end NatCodec

end Cslib.Complexity
