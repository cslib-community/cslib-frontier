/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Primitives.ByteString
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Fintype.Sort

/-!
# Programming the raw challenge-expansion row of ML-DSA

This implementation chooses the 221-byte minimum permitted by [FIPS 204][NISTFIPS204],
Appendix C, Table 3, for bounded Algorithm 29. The insertion positions on a successful
bounded row encode an ordered support. Transporting their final positions backward through the
swaps changes only accepted candidate bytes. Sorting the source and target supports gives an
invertible relabeling. The used sign bits are set from the target at each label’s destination.
Rejected candidates, the unconsumed suffix and unused sign bits retain their exact values.

The row exchange and its distribution theorem are original. `uniform_exchangeSampleInBall`
gives the joint law of the entire raw row and the optional challenge, including exhaustion.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

namespace ChallengeRow

private def Trace.raw {i n : ℕ} : Trace i n → List Byte
  | .done tail => tail
  | .reject b _ t | .accept b _ t => b :: t.raw

private theorem Trace.parse_raw {i n : ℕ} (t : Trace i n) : parse i n t.raw = some t := by
  induction t with
  | done => rw [Trace.raw, parse]
  | reject b h t ih => simp [Trace.raw, parse, h, ih]
  | accept b h t ih => simp [Trace.raw, parse, Nat.not_lt_of_ge h, ih]

private theorem raw_of_parse {i n : ℕ} {xs : List Byte} {t : Trace i n}
    (h : parse i n xs = some t) : t.raw = xs := by
  induction xs generalizing i n with
  | nil =>
    cases n with
    | zero => simp only [parse, Option.some.injEq] at h; subst t; rfl
    | succ => simp [parse] at h
  | cons b xs ih =>
    cases n with
    | zero => simp only [parse, Option.some.injEq] at h; subst t; rfl
    | succ k =>
      rw [parse] at h
      split at h <;> obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h <;>
        exact congrArg (b :: ·) (ih hu)

@[ext] private structure FixedAbove (i : ℕ) where
  e : Equiv.Perm Byte
  fixes : ∀ j : Byte, i ≤ j.val → e j = j

private def FixedAbove.symm {i : ℕ} (p : FixedAbove i) : FixedAbove i :=
  ⟨p.e.symm, fun j hj => p.e.symm_apply_eq.mpr (p.fixes j hj).symm⟩

private theorem FixedAbove.below {i : ℕ} (p : FixedAbove (i + 1)) (b : Byte) (hb : b.val ≤ i) :
    (p.e b).val ≤ i := by
  by_contra h
  have fix := p.fixes (p.e b) (by lia)
  have eq := p.e.injective fix
  rw [eq] at h
  exact h hb

-- Before the insertion, conjugating by its old and new swaps leaves the current index fixed.
private def FixedAbove.step {i : ℕ} (p : FixedAbove (i + 1)) (b : Byte) (hb : b.val ≤ i)
    (hi : i < 256) : FixedAbove i :=
  let k : Byte := ⟨i, hi⟩
  ⟨((Equiv.swap k b).trans p.e).trans (Equiv.swap k (p.e b)), fun j hj => by
    by_cases hjk : j = k
    · subst j
      simp
    · have hj' : i + 1 ≤ j.val := by
        have ne : j.val ≠ i := fun h => hjk (Fin.ext h)
        lia
      have hbj : j ≠ b := fun h => by subst j; lia
      have hcj : j ≠ p.e b := fun h => by have := p.below b hb; rw [← h] at this; lia
      simp [Equiv.swap_apply_of_ne_of_ne hjk hbj, p.fixes j hj',
        Equiv.swap_apply_of_ne_of_ne hjk hcj]⟩

-- Walk backward from the final support permutation. A rejected draw has no swap to undo.
private def Trace.move {i n : ℕ} (t : Trace i n) (bound : i + n ≤ 256)
    (p : FixedAbove (i + n)) : Trace i n × FixedAbove i :=
  match t with
  | .done tail => (.done tail, p)
  | .reject b h t =>
    let (u, q) := t.move bound p
    (.reject b h u, q)
  | .accept (i := i) (n := k) b h t =>
    let (u, q) := t.move (by lia) ⟨p.e, fun j hj => p.fixes j (by lia)⟩
    (.accept (q.e b) (q.below b h) u, q.step b h (by lia))

private theorem Trace.move_perm {i n : ℕ} (t : Trace i n) (h : i + n ≤ 256)
    (p : FixedAbove (i + n)) (j : Byte) :
    (t.move h p).1.perm ((t.move h p).2.e j) = p.e (t.perm j) := by
  induction t generalizing j with
  | done => rfl
  | reject b hb t ih => exact ih _ _ j
  | @accept i n b hb t ih =>
    let q : FixedAbove ((i + 1) + n) := ⟨p.e, fun k hk => p.fixes k (by lia)⟩
    let out := t.move (by lia) q
    let k : Byte := ⟨i, by lia⟩
    have hk : Fin.ofNat 256 i = k := Fin.ext (Nat.mod_eq_of_lt (by lia))
    change out.1.perm (Equiv.swap (Fin.ofNat 256 i) (out.2.e b)
      (Equiv.swap k (out.2.e b) (out.2.e (Equiv.swap k b j)))) = p.e (t.perm _)
    rw [hk, Equiv.swap_apply_self]
    exact ih _ q (Equiv.swap k b j)

private theorem Trace.move_symm {i n : ℕ} (t : Trace i n) (h : i + n ≤ 256)
    (p : FixedAbove (i + n)) :
    (t.move h p).1.move h p.symm = (t, (t.move h p).2.symm) := by
  induction t with
  | done => rfl
  | reject b hb t ih =>
    simp only [Trace.move]
    rw [ih]
  | @accept i n b hb t ih =>
    let q : FixedAbove ((i + 1) + n) := ⟨p.e, fun k hk => p.fixes k (by lia)⟩
    let out := t.move (by lia) q
    have back := ih (by lia) q
    change out.1.move _ q.symm = (t, out.2.symm) at back
    let rebuild (z : Trace (i + 1) n × FixedAbove (i + 1)) :=
      (Trace.accept (z.2.e (out.2.e b)) (z.2.below _ (out.2.below b hb)) z.1,
        z.2.step (out.2.e b) (out.2.below b hb) (by lia))
    change rebuild (out.1.move _ q.symm) = _
    refine (congrArg rebuild back).trans ?_
    apply Prod.ext
    · simp [rebuild, FixedAbove.symm]
    · apply FixedAbove.ext
      ext j
      simp [rebuild, Trace.move, FixedAbove.step, FixedAbove.symm, out, q]

private def Trace.pattern {i n : ℕ} : Trace i n → List (Option Byte)
  | .done tail => tail.map some
  | .reject b _ t => some b :: t.pattern
  | .accept _ _ t => none :: t.pattern

private theorem Trace.pattern_move {i n : ℕ} (t : Trace i n) (h : i + n ≤ 256)
    (p : FixedAbove (i + n)) : (t.move h p).1.pattern = t.pattern := by
  induction t with
  | done => rfl
  | reject b _ t ih => exact congrArg (some b :: ·) (ih ..)
  | accept _ _ t ih => exact congrArg (none :: ·) (ih ..)

private theorem Trace.length_pattern {i n : ℕ} (t : Trace i n) :
    t.pattern.length = t.raw.length := by
  induction t <;> simp_all [Trace.pattern, Trace.raw]

/-- A signed weight-τ challenge, as returned by the sparse challenge oracle. -/
abbrev Target (s : Level) := {c : Poly // InBall s.params.τ c}

instance (s : Level) : Nonempty (Target s) :=
  ⟨⟨_, inBall_signedTail s (List.replicate 64 false) (Equiv.refl _)⟩⟩

private def Target.support {s : Level} (c : Target s) : Finset Byte :=
  Finset.univ.filter fun i => c.val i ≠ 0

private def Target.positions {s : Level} (c : Target s) :
    Fin s.params.τ ⊕ Fin (256 - s.params.τ) ≃ Byte :=
  finSumEquivOfFinset (s := c.support) c.property.2 (by
    rw [Finset.card_compl, Fintype.card_fin]
    exact congrArg (256 - ·) c.property.2)

private theorem Target.left_positions {s : Level} (c : Target s) (i : Fin s.params.τ) :
    c.val (c.positions (.inl i)) ≠ 0 := by
  exact (Finset.mem_filter.mp (c.support.orderEmbOfFin_mem c.property.2 i)).2

private theorem Target.right_positions {s : Level} (c : Target s) (i : Fin (256 - s.params.τ)) :
    c.val (c.positions (.inr i)) = 0 := by
  have h : c.positions (.inr i) ∈ c.supportᶜ :=
    (c.supportᶜ.orderIsoOfFin (by
      rw [Finset.card_compl, Fintype.card_fin]
      exact congrArg (256 - ·) c.property.2) i).property
  exact not_not.mp fun hn => (Finset.mem_compl.mp h) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)

private def Target.transfer {s : Level} (c d : Target s) : FixedAbove 256 :=
  ⟨c.positions.symm.trans d.positions, fun j h => by have := j.isLt; lia⟩

private theorem Target.transfer_nonzero {s : Level} (c d : Target s) (j : Byte) :
    d.val ((c.transfer d).e j) ≠ 0 ↔ c.val j ≠ 0 := by
  obtain ⟨x, rfl⟩ := c.positions.surjective j
  cases x with
  | inl i => simp [Target.transfer, c.left_positions, d.left_positions]
  | inr i => simp [Target.transfer, c.right_positions, d.right_positions]

private abbrev start (s : Level) := 256 - s.params.τ

private theorem span_level (s : Level) : start s + s.params.τ = 256 := by cases s <;> decide
private theorem signs_fit (s : Level) : s.params.τ ≤ 64 := by cases s <;> decide

private def label {s : Level} (j : ℕ) (hj : j < s.params.τ) : Byte :=
  ⟨start s + j, by have := span_level s; lia⟩

private theorem label_coeff {s : Level} (signs : Fin 64 → Bool) {j : ℕ} (hj : j < s.params.τ) :
    signedTail s (List.ofFn signs) (label j hj) =
      if signs ⟨j, lt_of_lt_of_le hj (signs_fit s)⟩ then -1 else 1 := by
  have hj' := lt_of_lt_of_le hj (signs_fit s)
  have get : (List.ofFn signs)[j]! = signs ⟨j, hj'⟩ := by
    rw [getElem!_pos _ _ (by simpa only [List.length_ofFn] using hj'), List.getElem_ofFn]
  simp only [signedTail, label, Nat.not_lt_of_ge (Nat.le_add_right ..), ↓reduceIte,
    Nat.add_sub_cancel_left, get]

private theorem Target.coeff_of_ne {s : Level} (c : Target s) (j : Byte) (h : c.val j ≠ 0) :
    (if c.val j = -1 then -1 else 1) = c.val j := by
  have b := abs_le.mp (c.property.1 j)
  have hz : (c.val j).valMinAbs ≠ 0 := fun e => h (by
    simpa using congrArg (fun a : ℤ => (a : ZMod 8380417)) e)
  have cases : (c.val j).valMinAbs = -1 ∨ (c.val j).valMinAbs = 1 := by lia
  rcases cases with e | e <;>
    have v := congrArg (fun a : ℤ => (a : ZMod 8380417)) e <;> simp only [ZMod.coe_valMinAbs] at v
  · rw [v]; decide
  · rw [v]; decide

@[ext] private structure Success (s : Level) where
  signs : Fin 64 → Bool
  trace : Trace (start s) s.params.τ

private def Success.challenge {s : Level} (x : Success s) : Target s :=
  ⟨signedTail s (List.ofFn x.signs) ∘ x.trace.perm.symm, inBall_signedTail ..⟩

private def moved {s : Level} (t : Trace (start s) s.params.τ) (c d : Target s) :=
  t.move (span_level s).le ⟨(c.transfer d).e, fun k hk =>
    (c.transfer d).fixes k (by rwa [span_level] at hk)⟩

private def Success.program {s : Level} (x : Success s) (d : Target s) : Success s :=
  let u := (moved x.trace x.challenge d).1
  ⟨fun j => if hj : j.val < s.params.τ then decide (d.val (u.perm (label j.val hj)) = -1)
    else x.signs j, u⟩

private theorem Success.challenge_program {s : Level} (x : Success s) (d : Target s) :
    (x.program d).challenge = d := by
  let u := moved x.trace x.challenge d
  apply Subtype.ext
  funext j
  obtain ⟨k, rfl⟩ := u.1.perm.surjective j
  change signedTail s (List.ofFn (x.program d).signs) (u.1.perm.symm (u.1.perm k)) = _
  rw [Equiv.symm_apply_apply]
  let k' := u.2.e.symm k
  have route : u.1.perm k = (x.challenge.transfer d).e (x.trace.perm k') := by
    have h := x.trace.move_perm (span_level s).le
      (FixedAbove.mk (x.challenge.transfer d).e (fun k h => (x.challenge.transfer d).fixes k
        (by rwa [span_level] at h))) k'
    change u.1.perm (u.2.e k') = _ at h
    simpa [k'] using h
  have supp := x.challenge.transfer_nonzero d (x.trace.perm k')
  rw [← route] at supp
  change d.val (u.1.perm k) ≠ 0 ↔ signedTail s (List.ofFn x.signs)
    (x.trace.perm.symm (x.trace.perm k')) ≠ 0 at supp
  rw [Equiv.symm_apply_apply] at supp
  by_cases hk : k.val < start s
  · have hk' : k'.val < start s := by
      by_contra! h
      have he := u.2.fixes k' h
      have eq : k = k' := by simpa [k'] using he
      lia
    simpa [signedTail, hk] using (show d.val (u.1.perm k) = 0 by
      simpa [signedTail, hk'] using supp).symm
  · let a := k.val - start s
    have ha : a < s.params.τ := by have := span_level s; have := k.isLt; dsimp [a]; lia
    have key : label a ha = k := Fin.ext (by dsimp [label, a]; lia)
    rw [← key, label_coeff]
    have old : k' = k := u.2.e.symm_apply_eq.mpr (u.2.fixes k (by lia)).symm
    have nz : d.val (u.1.perm k) ≠ 0 := supp.mpr (by
      rw [old, ← key, label_coeff]
      split <;> decide)
    simpa [Success.program, ha, u, key] using d.coeff_of_ne (u.1.perm k) nz

private theorem Success.program_back {s : Level} (x : Success s) (d : Target s) :
    (x.program d).program x.challenge = x := by
  let u := moved x.trace x.challenge d
  have back : (moved u.1 d x.challenge).1 = x.trace := by
    exact congrArg Prod.fst (x.trace.move_symm (span_level s).le
      (FixedAbove.mk (x.challenge.transfer d).e (fun k h => (x.challenge.transfer d).fixes k
        (by rwa [span_level] at h))))
  have tr : (moved (x.program d).trace (x.program d).challenge x.challenge).1 = x.trace := by
    rw [x.challenge_program]
    exact back
  apply Success.ext ?_ tr
  funext j
  by_cases hj : j.val < s.params.τ
  · change (if h : j.val < s.params.τ then decide (x.challenge.val
      ((moved (x.program d).trace (x.program d).challenge x.challenge).1.perm (label j.val h)) = -1)
      else (x.program d).signs j) = x.signs j
    rw [dite_eq_left hj, tr]
    change decide (signedTail s (List.ofFn x.signs)
      (x.trace.perm.symm (x.trace.perm (label j.val hj))) = -1) = x.signs j
    rw [Equiv.symm_apply_apply, label_coeff]
    cases x.signs j <;> decide
  · simp [Success.program, hj]

private def readSigns (head : List Byte) (j : Fin 64) : Bool :=
  (Keccak.bytesToBitsLE head)[j.val]!

private def signBytes (signs : Fin 64 → Bool) : List Byte :=
  ((List.ofFn signs).toChunks 8).map Keccak.bitsToByteLE

private theorem bits_signBytes (signs : Fin 64 → Bool) :
    Keccak.bytesToBitsLE (signBytes signs) = List.ofFn signs :=
  Keccak.bytesToBitsLE_toChunks (by simp)

private theorem length_signBytes (signs : Fin 64 → Bool) : (signBytes signs).length = 8 := by
  have h := congrArg List.length (bits_signBytes signs)
  rw [Keccak.length_bytesToBitsLE, List.length_ofFn] at h
  lia

private theorem ofFn_read! {α : Type} [Inhabited α] {xs : List α} {n : ℕ} (h : xs.length = n) :
    List.ofFn (fun j : Fin n => xs[j.val]!) = xs := by
  subst n
  trans List.ofFn xs.get
  · congr 1
    funext j
    exact getElem!_pos xs j.val j.isLt
  · exact List.ofFn_get _

private theorem bits_readSigns {head : List Byte} (h : head.length = 8) :
    List.ofFn (readSigns head) = Keccak.bytesToBitsLE head :=
  ofFn_read! (by rw [Keccak.length_bytesToBitsLE, h])

private theorem signBytes_readSigns {head : List Byte} (h : head.length = 8) :
    signBytes (readSigns head) = head :=
  Keccak.bytesToBitsLE_injective ((bits_signBytes (readSigns head)).trans (bits_readSigns h))

private theorem readSigns_signBytes (signs : Fin 64 → Bool) :
    readSigns (signBytes signs) = signs := by
  apply List.ofFn_injective
  rw [bits_readSigns (length_signBytes _), bits_signBytes]

private def decode (s : Level) (xs : List Byte) : Option (Success s) :=
  (parse (start s) s.params.τ (xs.drop 8)).map fun t => ⟨readSigns (xs.take 8), t⟩

private def Success.raw {s : Level} (x : Success s) := signBytes x.signs ++ x.trace.raw

private theorem Success.decode_raw {s : Level} (x : Success s) : decode s x.raw = some x := by
  simp [decode, Success.raw, List.take_left' (length_signBytes _),
    List.drop_left' (length_signBytes _), Trace.parse_raw, readSigns_signBytes]

private theorem Success.raw_of_decode {s : Level} {xs : List Byte} (h : 8 ≤ xs.length)
    {x : Success s} (hx : decode s xs = some x) : x.raw = xs := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hx
  change signBytes (readSigns _) ++ t.raw = _
  rw [raw_of_parse ht, signBytes_readSigns (by simp [h]), List.take_append_drop]

private theorem Success.length_program {s : Level} (x : Success s) (d : Target s) :
    (x.program d).raw.length = x.raw.length := by
  simp only [Success.raw, List.length_append, length_signBytes]
  congr 1
  rw [← Trace.length_pattern, ← Trace.length_pattern x.trace]
  exact congrArg List.length (x.trace.pattern_move ..)

private theorem sample_decode (s : Level) (xs : List Byte) (h : 8 ≤ xs.length) :
    sampleInBallBytes s xs = (decode s xs).map fun x => x.challenge.val := by
  unfold sampleInBallBytes decode
  cases parse (start s) s.params.τ (xs.drop 8) with
  | none => rfl
  | some t =>
    change some (signedTail s _ ∘ t.perm.symm) = some
      (signedTail s (List.ofFn (readSigns (xs.take 8))) ∘ t.perm.symm)
    rw [bits_readSigns (by simp [h])]

private def bytesOfList (xs : List Byte) : FixedBytes 221 := fun j => xs[j.val]!

private theorem toList_bytesOfList {xs : List Byte} (h : xs.length = 221) :
    (bytesOfList xs).toList = xs := ofFn_read! h

private def exchange (s : Level) (r : FixedBytes 221 × Target s) : FixedBytes 221 × Target s :=
  match decode s r.1.toList with
  | none => r
  | some x => (bytesOfList (x.program r.2).raw, x.challenge)

private theorem exchange_involutive (s : Level) : Function.Involutive (exchange s) := by
  intro (row, d)
  cases hd : decode s row.toList with
  | none => simp [exchange, hd]
  | some x =>
    have hr := x.raw_of_decode (by simp) hd
    have len : (x.program d).raw.length = 221 := by rw [x.length_program, hr]; simp
    simp only [exchange, hd, toList_bytesOfList len, Success.decode_raw, Success.challenge_program,
      Success.program_back, hr, Prod.mk.injEq, and_true]
    funext j
    change (List.ofFn row)[j.val]! = row j
    rw [getElem!_pos _ _ (by simpa only [List.length_ofFn] using j.isLt), List.getElem_ofFn]

/-- Exchange a supplied signed sparse challenge with the challenge decoded from a bounded
Algorithm 29 row. On exhaustion the complete row and the supplied challenge are unchanged.
On success the inverse is the same operation with the original challenge. -/
def exchangeSampleInBall (s : Level) :
    FixedBytes 221 × Target s ≃ FixedBytes 221 × Target s :=
  (exchange_involutive s).toPerm _

/-- Two forward exchanges restore the raw bytes and the supplied challenge. -/
theorem exchangeSampleInBall_involutive (s : Level) :
    Function.Involutive (exchangeSampleInBall s) :=
  exchange_involutive s

/-- Exactly the candidate bytes untouched by Algorithm 29 programming. On a successful row,
accepted positions are holes, while rejected positions and the unused suffix retain their bytes
at their original offsets. An exhausted row has no successful pattern. -/
def retainedCandidates (s : Level) (row : FixedBytes 221) : Option (List (Option Byte)) :=
  (decode s row.toList).map fun x => x.trace.pattern

/-- On an exhausted row, programming changes no bytes and returns the still unused challenge. -/
theorem exchangeSampleInBall_of_none {s : Level} {row : FixedBytes 221}
    (h : sampleInBallBytes s row.toList = none) (d : Target s) :
    exchangeSampleInBall s (row, d) = (row, d) := by
  rw [sample_decode s _ (by simp)] at h
  cases hd : decode s row.toList with
  | none => simp [exchangeSampleInBall, Function.Involutive.toPerm, exchange, hd]
  | some x => simp [hd] at h

/-- On success the programmed bytes decode to the supplied challenge, and the second output
is the challenge originally decoded from the row. -/
theorem exchangeSampleInBall_of_some {s : Level} {row : FixedBytes 221} {c : Poly}
    (h : sampleInBallBytes s row.toList = some c) (d : Target s) :
    sampleInBallBytes s (exchangeSampleInBall s (row, d)).1.toList = some d.val ∧
      (exchangeSampleInBall s (row, d)).2.val = c := by
  rw [sample_decode s _ (by simp)] at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have len : (x.program d).raw.length = 221 := by
    rw [x.length_program, x.raw_of_decode (by simp) hx]; simp
  change sampleInBallBytes s (exchange s (row, d)).1.toList = _ ∧ (exchange s (row, d)).2.val = _
  simp only [exchange, hx, toList_bytesOfList len]
  rw [sample_decode _ _ (by rw [len]; decide), Success.decode_raw]
  simp [Success.challenge_program]

/-- The permutation restricted to successful rows gives an explicit bijection from the
preimages of any signed challenge to the preimages of any other. The inverse programs the
original challenge back into the row. -/
def fiberEquiv {s : Level} (c d : Target s) :
    {r : FixedBytes 221 // sampleInBallBytes s r.toList = some c.val} ≃
    {r : FixedBytes 221 // sampleInBallBytes s r.toList = some d.val} :=
  let fiber (a : Target s) := {r : FixedBytes 221 // sampleInBallBytes s r.toList = some a.val}
  let forward (a b : Target s) (r : fiber a) :
      fiber b :=
    ⟨(exchangeSampleInBall s (r.val, b)).1, (exchangeSampleInBall_of_some r.property b).1⟩
  let back (a b : Target s) (r : fiber a) :
      forward b a (forward a b r) = r := by
    have h : (exchangeSampleInBall s (r.val, b)).2 = a :=
      Subtype.ext (exchangeSampleInBall_of_some r.property b).2
    apply Subtype.ext
    change (exchangeSampleInBall s ((exchangeSampleInBall s (r.val, b)).1, a)).1 = r.val
    exact (congrArg (fun t =>
      (exchangeSampleInBall s ((exchangeSampleInBall s (r.val, b)).1, t)).1) h.symm).trans
        (congrArg Prod.fst (exchangeSampleInBall_involutive s (r.val, b)))
  ⟨forward c d, forward d c, back c d, back d c⟩

/-- Programming preserves the unused sign bits and every rejected or unconsumed candidate byte. -/
theorem exchangeSampleInBall_retains (s : Level) (row : FixedBytes 221) (d : Target s) :
    let new := (exchangeSampleInBall s (row, d)).1
    (Keccak.bytesToBitsLE (new.toList.take 8)).drop s.params.τ =
        (Keccak.bytesToBitsLE (row.toList.take 8)).drop s.params.τ ∧
      retainedCandidates s new = retainedCandidates s row := by
  cases hx : decode s row.toList with
  | none => simp [exchangeSampleInBall, Function.Involutive.toPerm, exchange, hx]
  | some x =>
    have hr := x.raw_of_decode (by simp) hx
    have len : (x.program d).raw.length = 221 := by rw [x.length_program, hr]; simp
    simp only [exchangeSampleInBall, Function.Involutive.toPerm, Equiv.coe_fn_mk, exchange, hx,
      toList_bytesOfList len, retainedCandidates, Success.decode_raw, Option.map_some,
      Option.some.injEq]
    constructor
    · rw [← hr]
      simp only [Success.raw, List.take_left' (length_signBytes _), bits_signBytes]
      apply List.ext_getElem (by simp only [List.length_drop, List.length_ofFn])
      intro j hj hj'
      simp only [List.getElem_drop, List.getElem_ofFn]
      exact dite_eq_right (by lia)
    · exact x.trace.pattern_move ..

/-- Joint law of the complete 221-byte raw row and its Algorithm 29 result. Start with uniform
bytes and an independent uniform signed weight-τ challenge. Program the row and report the
supplied challenge on success, or the original exhaustion. This has exactly the law of reading
Algorithm 29 on a single uniform byte row. -/
theorem uniform_exchangeSampleInBall (s : Level) :
    (Probability.PMF.uniformOfFintype (FixedBytes 221 × Target s)).map (fun (row, d) =>
      ((exchangeSampleInBall s (row, d)).1, (sampleInBallBytes s row.toList).map fun _ => d.val)) =
    (Probability.PMF.uniformOfFintype (FixedBytes 221)).map (fun row =>
      (row, sampleInBallBytes s row.toList)) := by
  apply Probability.PMF.uniformOfFintype_map_exchange_option
    (exchangeSampleInBall s) (fun row => sampleInBallBytes s row.toList) Subtype.val
  · exact fun h d => by rw [exchangeSampleInBall_of_none h d]; exact h
  · exact fun h d => (exchangeSampleInBall_of_some h d).1

end ChallengeRow

end Cslib.Crypto.MLDSA.FIPS204
