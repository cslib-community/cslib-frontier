/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators

/-!
# Ranked trees for a soft heap

[Brodal2021SoftSequenceHeaps], §4, describes heap-ordered trees of any fixed arity at least
three. This module uses four children. A linked root pulls one bucket from its least child.
During extraction a high-rank node pulls a second bucket and gives both buckets one current key.
The number of items assigned to another representative is bounded on every tree reachable by
linking and extraction.
-/

public section

namespace Cslib.SoftHeap

/-- The representative supplies the current key of every item in this bucket. -/
structure Bucket (α : Type) where
  /-- Item retaining its input key. -/
  rep : α
  /-- Items sharing the current key of the representative. -/
  pending : List α

variable {α : Type}

namespace Bucket

/-- A bucket with an unraised item. -/
@[expose] def singleton (a : α) : Bucket α := ⟨a, []⟩

/-- Pool two nonempty buckets, retaining the larger representative. -/
@[expose] def pool {W : Type*} [LinearOrder W] (w : α → W) (a b : Bucket α) : Bucket α :=
  if w a.rep ≤ w b.rep then ⟨b.rep, a.rep :: a.pending ++ b.pending⟩
  else ⟨a.rep, b.rep :: b.pending ++ a.pending⟩

/-- The current key dominates all original keys. -/
def Raised {W : Type*} [LE W] (w : α → W) (b : Bucket α) : Prop :=
  ∀ x ∈ b.pending, w x ≤ w b.rep

theorem pool_raised {W : Type*} [LinearOrder W] {w : α → W} {a b : Bucket α}
    (ha : a.Raised w) (hb : b.Raised w) : (pool w a b).Raised w := by
  unfold pool
  split
  · next h =>
      intro x hx
      simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with (rfl | h') | h'
      · exact h
      · exact (ha _ h').trans h
      · exact hb _ h'
  · next h =>
      have le := le_of_not_ge h
      intro x hx
      simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with (rfl | h') | h'
      · exact le
      · exact (hb _ h').trans le
      · exact ha _ h'

@[simp] theorem length_pool {W : Type*} [LinearOrder W] (w : α → W) (a b : Bucket α) :
    (pool w a b).pending.length = a.pending.length + b.pending.length + 1 := by
  unfold pool
  split <;> simp [Nat.add_comm]

end Bucket

/-- A tree of rank `r` records exactly `4 ^ r` insertion leaves, including empty leaves. -/
inductive Tree (α : Type) : ℕ → Type
  | leaf (bucket : Option (Bucket α)) : Tree α 0
  | node {r : ℕ} (bucket : Option (Bucket α)) (children : Fin 4 → Tree α r) : Tree α (r + 1)

namespace Tree

variable {r : ℕ}

/-- Root bucket of a ranked tree. -/
@[expose] def root : {r : ℕ} → Tree α r → Option (Bucket α)
  | _, .leaf b | _, .node b _ => b

/-- Choose the nonempty child with the smallest representative key. -/
@[expose] def leastChild {W : Type*} [LinearOrder W] (w : α → W) (cs : Fin 4 → Tree α r) :
    Option (Fin 4 × Bucket α) :=
  ((List.finRange 4).filterMap fun i => (cs i).root.map (i, ·)).minOn? (fun p => w p.2.rep)

theorem root_of_leastChild {W : Type*} [LinearOrder W] {w : α → W} {cs : Fin 4 → Tree α r}
    {i b} (h : leastChild w cs = some (i, b)) : (cs i).root = some b := by
  have mem := List.minOn?_mem h
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp mem
  cases e : (cs j).root <;> simp only [e, Option.map_none, Option.map_some, Option.some.injEq,
    Prod.mk.injEq, reduceCtorEq] at hj
  obtain ⟨rfl, rfl⟩ := hj
  exact e

/-- Pull the least child bucket and refill the child where it was located. -/
@[expose] def pull {W : Type*} [LinearOrder W] (w : α → W) (next : Tree α r → Tree α r)
    (cs : Fin 4 → Tree α r) : Option (Bucket α) × (Fin 4 → Tree α r) :=
  match leastChild w cs with
  | none => (none, cs)
  | some (i, b) => (some b, Function.update cs i (next (cs i)))

/-- Fill a node after removing its old bucket. The linking mode draws one child at each
level. Extraction can draw two above the rank threshold, merging their current keys. -/
@[expose] def refill {W : Type*} [LinearOrder W] (w : α → W) (threshold : ℕ)
    (soft : Bool) : {r : ℕ} → Tree α r → Tree α r
  | 0, .leaf _ => .leaf none
  | r + 1, .node _ cs =>
    let next := refill w threshold soft (r := r)
    let (first, cs') := pull w next cs
    if soft && decide (threshold < r + 1) then
      match first with
      | none => .node none cs'
      | some a =>
        let (second, cs'') := pull w next cs'
        .node (some (second.elim a (Bucket.pool w a))) cs''
    else .node first cs'

/-- Create the tree for a single insertion. -/
@[expose] def singleton (a : α) : Tree α 0 := .leaf (some (.singleton a))

/-- Link four trees of equal rank, creating a root without raising any new keys. -/
@[expose] def link {W : Type*} [LinearOrder W] (w : α → W) (threshold : ℕ)
    (cs : Fin 4 → Tree α r) : Tree α (r + 1) :=
  refill w threshold false (.node none cs)

/-- Replace the root bucket after extracting one of its pending items. -/
@[expose] def setRoot (b : Option (Bucket α)) : {r : ℕ} → Tree α r → Tree α r
  | _, .leaf _ => .leaf b
  | _, .node _ cs => .node b cs

/-- Return an item and its current representative. A representative itself is extracted only
when its pending list is empty. -/
@[expose] def extract {W : Type*} [LinearOrder W] (w : α → W) (threshold : ℕ) (t : Tree α r) :
    Option ((α × α) × Tree α r) :=
  match t.root with
  | none => none
  | some ⟨a, []⟩ => some ((a, a), refill w threshold true t)
  | some ⟨a, x :: xs⟩ => some ((x, a), t.setRoot (some ⟨a, xs⟩))

/-- The per-rank list bound includes the representative itself. -/
def BucketOK {W : Type*} [LE W] (w : α → W) (t r : ℕ) (slot : Option (Bucket α)) : Prop :=
  ∀ b, slot = some b → b.Raised w ∧ b.pending.length < 2 ^ (r-t)

/-- Every occupied bucket has raised keys and meets its rank capacity. -/
def Valid {W : Type*} [LE W] (w : α → W) (t : ℕ) : {r : ℕ} → Tree α r → Prop
  | 0, .leaf b => BucketOK w t 0 b
  | r + 1, .node b cs => BucketOK w t (r + 1) b ∧ ∀ i, Valid w t (cs i)

private theorem valid_root {W : Type*} [LE W] {w : α → W} {t : ℕ}
    {tr : Tree α r} (h : tr.Valid w t) : BucketOK w t r tr.root := by
  cases tr with
  | leaf => exact h
  | node => exact h.1

private theorem emptyOK {W : Type*} [LE W] {w : α → W} {t r : ℕ} :
    BucketOK w t r none := by simp [BucketOK]

private theorem promote {W : Type*} [LE W] {w : α → W} {t r : ℕ} {s : Option (Bucket α)}
    (h : BucketOK w t r s) : BucketOK w t (r + 1) s := by
  intro b eq
  obtain ⟨raised, len⟩ := h b eq
  exact ⟨raised, len.trans_le (Nat.pow_le_pow_right (by omega) (by omega))⟩

private theorem pull_valid {W : Type*} [LinearOrder W] (w : α → W) (t : ℕ)
    (next : Tree α r → Tree α r) (pres : ∀ tr, tr.Valid w t → (next tr).Valid w t)
    (cs : Fin 4 → Tree α r) (ok : ∀ i, (cs i).Valid w t) :
    BucketOK w t r (pull w next cs).1 ∧ ∀ i, ((pull w next cs).2 i).Valid w t := by
  unfold pull
  cases h : leastChild w cs with
  | none => exact ⟨emptyOK, ok⟩
  | some p =>
    obtain ⟨j, b⟩ := p
    refine ⟨?_, ?_⟩
    · simpa [root_of_leastChild h] using valid_root (ok j)
    · intro i
      by_cases e : i = j
      · subst i
        simpa using pres _ (ok j)
      · simpa [Function.update_of_ne e] using ok i

theorem refill_valid {W : Type*} [LinearOrder W] (w : α → W) (t : ℕ) (soft : Bool)
    (tr : Tree α r) (ok : tr.Valid w t) : (refill w t soft tr).Valid w t := by
  induction r with
  | zero => cases tr; exact emptyOK
  | succ r ih =>
    cases tr with
    | node _ cs =>
      let next := refill w t soft (r := r)
      generalize hfirst : pull w next cs = result
      obtain ⟨a, cs'⟩ := result
      have ⟨ha, hc⟩ := pull_valid w t next ih cs ok.2
      rw [hfirst] at ha hc
      simp only [refill, show refill w t soft (r := r) = next from rfl, hfirst]
      split
      · next enabled =>
          cases a with
          | none => exact ⟨emptyOK, hc⟩
          | some a =>
            generalize hsecond : pull w next cs' = result
            obtain ⟨b, cs''⟩ := result
            have ⟨hb, hc'⟩ := pull_valid w t next ih cs' hc
            rw [hsecond] at hb hc'
            dsimp only
            refine ⟨?_, hc'⟩
            cases b with
            | none => exact promote ha
            | some b =>
              intro z hz
              obtain rfl := Option.some.inj hz
              obtain ⟨ra, la⟩ := ha a rfl
              obtain ⟨rb, lb⟩ := hb b rfl
              refine ⟨Bucket.pool_raised ra rb, ?_⟩
              have ht : t ≤ r := by simp at enabled; omega
              have e : r + 1-t = (r-t) + 1 := by omega
              simp only [Option.elim_some, Bucket.length_pool, e, Nat.pow_succ]
              omega
      · exact ⟨promote ha, hc⟩

theorem singleton_valid {W : Type*} [LinearOrder W] (w : α → W) (t : ℕ) (a : α) :
    (singleton a).Valid w t := by
  simp [singleton, Valid, BucketOK, Bucket.singleton, Bucket.Raised]

theorem link_valid {W : Type*} [LinearOrder W] (w : α → W) (t : ℕ) (cs : Fin 4 → Tree α r)
    (ok : ∀ i, (cs i).Valid w t) : (link w t cs).Valid w t :=
  refill_valid w t false _ ⟨emptyOK, ok⟩

private theorem setRoot_valid {W : Type*} [LE W] {w : α → W} {t : ℕ} {tr : Tree α r}
    (h : tr.Valid w t) {s : Option (Bucket α)} (hs : BucketOK w t r s) :
    (tr.setRoot s).Valid w t := by
  cases tr with
  | leaf => exact hs
  | node => exact ⟨hs, h.2⟩

theorem extract_valid {W : Type*} [LinearOrder W] {w : α → W} {t : ℕ} {tr tr' : Tree α r}
    {x a : α} (ok : tr.Valid w t) (hit : extract w t tr = some ((x, a), tr')) :
    w x ≤ w a ∧ tr'.Valid w t := by
  unfold extract at hit
  split at hit
  · contradiction
  · next b hb =>
      cases hit
      exact ⟨le_rfl, refill_valid w t true _ ok⟩
  · next b y ys hb =>
      cases hit
      obtain ⟨raised, len⟩ := valid_root ok _ hb
      refine ⟨raised _ (by simp), setRoot_valid ok ?_⟩
      intro z eq
      obtain rfl := Option.some.inj eq
      refine ⟨fun x hx => raised _ (List.mem_cons_of_mem _ hx), ?_⟩
      change ys.length < _
      simp only [List.length_cons] at len
      omega

/-- Number of live items assigned to another representative. Ties may make this an
overestimate of the number of keys that increased strictly. -/
@[expose] def corruptions : {r : ℕ} → Tree α r → ℕ
  | _, .leaf b => b.elim 0 (fun x => x.pending.length)
  | _, .node b cs => b.elim 0 (fun x => x.pending.length) + ∑ i, (cs i).corruptions

private def allowance (t : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => (2 ^ ((r + 1)-t)-1) + 4 * allowance t r

private theorem corruptions_le_allowance {W : Type*} [LE W] {w : α → W} {t : ℕ}
    (tr : Tree α r) (ok : tr.Valid w t) : tr.corruptions ≤ allowance t r := by
  have headBound {k : ℕ} {b : Option (Bucket α)} (h : BucketOK w t k b) :
      b.elim 0 (fun x => x.pending.length) ≤ 2 ^ (k-t)-1 := by
    cases b with
    | none => exact Nat.zero_le _
    | some a =>
      have len := (h a rfl).2
      change a.pending.length ≤ _
      omega
  induction r with
  | zero =>
    cases tr with
    | leaf b => simpa [corruptions, allowance] using headBound ok
  | succ k ih =>
    cases tr with
    | node b cs =>
      apply Nat.add_le_add (headBound ok.1)
      calc
        _ ≤ ∑ _ : Fin 4, allowance t k := Finset.sum_le_sum fun i _ => ih (cs i) (ok.2 i)
        _ = 4 * allowance t k := by simp

private theorem allowance_below {t r : ℕ} (h : r ≤ t) : allowance t r = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [allowance, Nat.sub_eq_zero_of_le h, ih (by omega)]

private theorem allowance_above (t d : ℕ) : allowance t (t + d) + 2 ^ d ≤ 4 ^ d := by
  induction d with
  | zero => simp [allowance_below]
  | succ d ih =>
    have h : t + d.succ = (t + d) + 1 := by omega
    rw [h, allowance, show t + d + 1-t = d + 1 by omega, Nat.pow_succ, Nat.pow_succ]
    omega

/-- On a rank `r` tree, a fraction at most `1 / 4 ^ t` of its `4 ^ r` insertion leaves can
currently have a different representative. -/
theorem corruptions_bound {W : Type*} [LE W] {w : α → W} {t : ℕ}
    (tr : Tree α r) (ok : tr.Valid w t) : tr.corruptions * 4 ^ t ≤ 4 ^ r := by
  have bound := corruptions_le_allowance tr ok
  by_cases h : r ≤ t
  · rw [allowance_below h] at bound
    rw [Nat.eq_zero_of_le_zero bound]
    simp
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge h)
    have slack := allowance_above t d
    rw [Nat.pow_add, Nat.mul_comm (4 ^ t)]
    exact Nat.mul_le_mul_right _ (bound.trans ((Nat.le_add_right _ _).trans slack))

end Tree
end Cslib.SoftHeap
