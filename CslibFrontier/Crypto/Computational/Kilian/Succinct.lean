/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Kilian
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Tactic.EncLen

/-!
# Succinctness of Kilian's protocol

Kilian's protocol is succinct: the honest transcript has a number of bits polynomial in the
security parameter and polylogarithmic in the encoded statement length ([Kilian1992];
[BarakGoldreich2001], Construction 3.4). This module counts it, in terms
of the PCP verifier's parameters, kept separate from them: `r = V.coins x` random bits and at most
`q` queries per random string.

* **The committed table.** The compact table has `|V.queryTable x| ≤ 2 ^ r * q` entries
  (`length_queryTable_le`), so the tree has depth `kilianDepth V x ≤ r + ⌈log₂ q⌉`
  (`kilianDepth_le`).
* **Communication.** `kilianCommunication` counts the payload bits of a transcript after the
  statement: the key, the root, the random strings, and for each opening its bit and its path
  labels. Message framing (the `encPair`/`encList` separators) and the statement `x` are not
  counted. For a hash with `n`-bit digests, an honest transcript at security parameter `n` has at
  most `2 * n + n * r + n * (q * (1 + (r + ⌈log₂ q⌉) * n))` bits
  (`kilianCommunication_honest_le`). With logarithmically many random bits and a constant number
  of queries, as for the verifier of the PCP theorem, this is `O(n² · (log₂ |enc x| + 1))`
  (`kilianCommunication_honest_le_log`).

Verifier time is certified by `computableInPolyTime_kilianVerify`, assuming a polynomial-time
hash with key-length digests, `V.PolyTime enc` and logarithmically many random bits. On honest
transcripts, the encoded verifier input has length linear in `|enc x|` and polynomial in `n` and
the PCP parameters (`length_kilianVerifierInput_honest_le`); combining the two under a constant
(or polynomial) query bound yields a single binary multi-tape Turing machine computing
`kilianVerify` whose step and space counts on every honest transcript are polynomially bounded in
`n + |enc x|` (`computableInTimeAndSpace_kilianVerify_honest_le`). The verifier does not truncate
oversized raw messages, so on arbitrary malformed inputs its time is polynomial in the received
encoded input length.

## Main definitions

* `Cslib.Crypto.kilianOpeningBits`, `Cslib.Crypto.kilianResponseBits`,
  `Cslib.Crypto.kilianCommunication`: payload bits of an opening, a response and a transcript.

## Main results

* `Cslib.Crypto.length_queryTable_le`, `Cslib.Crypto.kilianDepth_le`: size and depth of the
  committed table.
* `Cslib.Crypto.kilianResponseBits_kilianRespond_le`: the honest response.
* `Cslib.Crypto.kilianCommunication_honest_le`: honest communication in the PCP parameters.
* `Cslib.Crypto.kilianCommunication_honest_le_log`: `O(n² · (log₂ |enc x| + 1))` bits for
  logarithmic randomness and constant query complexity.
* `Cslib.Crypto.length_kilianVerifierInput_honest_le`: the encoded verifier input of an honest
  transcript is linear in the statement and polynomial in `n` and the PCP parameters.
* `Cslib.Crypto.computableInTimeAndSpace_kilianVerify_honest_le`: machine-level time and space
  bounds polynomial in `n + |enc x|` on every honest transcript.

## References

* [J. Kilian, *A note on efficient zero-knowledge proofs and arguments*][Kilian1992]
* [B. Barak, O. Goldreich, *Universal Arguments and their Applications*][BarakGoldreich2001],
  Construction 3.4.
-/

@[expose] public section

namespace Cslib.Crypto

open Complexity Turing.MultiTapeTM

variable {α : Type} {H : List Bool → List Bool → List Bool} {V : PCPVerifier α}

/-! ### Counting bits -/

/-- The payload bits of an opening: its bit and the bits of its path labels. -/
def kilianOpeningBits : MerkleOpening Bool → ℕ
  | o => 1 + (o.path.map List.length).sum

/-- The payload bits of a response: the bits of all its openings. -/
def kilianResponseBits (response : KilianResponse) : ℕ :=
  (response.map fun answers => (answers.map kilianOpeningBits).sum).sum

/-- The payload bits of a transcript after the statement: the key, the root, the random strings
and the response. -/
def kilianCommunication (k root : List Bool) (ρs : List (List Bool)) (response : KilianResponse) :
    ℕ :=
  k.length + root.length + (ρs.map List.length).sum + kilianResponseBits response

/-! ### The committed table -/

/-- The compact table has at most `2 ^ r * q` entries for a verifier using `r` random bits and at
most `q` queries per random string. -/
theorem length_queryTable_le {x : α} {q : ℕ}
    (hq : ∀ ρ : List Bool, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ q) :
    (V.queryTable x).length ≤ 2 ^ V.coins x * q := by
  rw [PCPVerifier.queryTable, List.length_flatMap]
  refine (List.sum_le_length_nsmul _ q fun m hm => ?_).trans (by simp)
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hm
  exact hq ρ (BitString.mem_enumList.mp hρ)

/-- The committed tree has depth at most `r + ⌈log₂ q⌉`. -/
theorem kilianDepth_le {x : α} {q : ℕ}
    (hq : ∀ ρ : List Bool, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ q) :
    kilianDepth V x ≤ V.coins x + Nat.clog 2 q := by
  rw [kilianDepth, Nat.clog_le_iff_le_pow (by norm_num), pow_add]
  exact (length_queryTable_le hq).trans
    (Nat.mul_le_mul_left _ (Nat.le_pow_clog (by norm_num) q))

/-! ### Honest communication -/

/-- **The honest response is short**: for a hash with `k.length`-bit digests, each of the
`ρs.length` repetitions sends at most `q` openings, each of one bit and `kilianDepth V x` labels of
at most `k.length` bits. -/
theorem kilianResponseBits_kilianRespond_le (hlen : ∀ k x, (H k x).length = k.length)
    {k : List Bool} {x : α} {table : List Bool} {ρs : List (List Bool)} {q : ℕ}
    (hq : ∀ ρ : List Bool, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ q)
    (hρs : ∀ ρ ∈ ρs, ρ.length = V.coins x) :
    kilianResponseBits (kilianRespond H V k x table ρs) ≤
      ρs.length * (q * (1 + kilianDepth V x * k.length)) := by
  rw [kilianResponseBits, kilianRespond, List.map_map]
  refine (List.sum_le_length_nsmul _ (q * (1 + kilianDepth V x * k.length))
    fun m hm => ?_).trans (by simp)
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hm
  simp only [Function.comp_apply, kilianOpen, List.map_map]
  refine (List.sum_le_length_nsmul _ (1 + kilianDepth V x * k.length) fun m hm => ?_).trans ?_
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hm
    have hpath : (merklePath H k (kilianLeaves (kilianTable V x table))
        (kilianPosition V x a)).length = kilianDepth V x := by
      simp [length_merklePath, kilianLeaves, kilianDepth]
    have hsum := List.sum_le_length_nsmul
      ((merklePath H k (kilianLeaves (kilianTable V x table)) (kilianPosition V x a)).map
        List.length) k.length fun m hm => by
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
          exact length_le_of_mem_merklePath hlen hs
    simp only [List.length_map, hpath, smul_eq_mul] at hsum
    simpa only [Function.comp_apply, kilianOpeningBits] using Nat.add_le_add_left hsum 1
  · simp only [List.length_map, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (hq ρ (hρs ρ hρ))

/-- **Honest communication** in the PCP parameters: at security parameter `n`, with an `n`-bit key,
`n` random strings of `r = V.coins x` bits and a hash with `n`-bit digests, the honest transcript
after the statement has at most `2 * n + n * r + n * (q * (1 + (r + ⌈log₂ q⌉) * n))` bits. -/
theorem kilianCommunication_honest_le (hlen : ∀ k x, (H k x).length = k.length)
    {n : ℕ} {k : List Bool} (hk : k.length = n) {x : α} {table : List Bool}
    {ρs : List (List Bool)} (hn : ρs.length = n) (hρs : ∀ ρ ∈ ρs, ρ.length = V.coins x) {q : ℕ}
    (hq : ∀ ρ : List Bool, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ q) :
    kilianCommunication k (kilianCommit H V k x table) ρs (kilianRespond H V k x table ρs) ≤
      2 * n + n * V.coins x + n * (q * (1 + (V.coins x + Nat.clog 2 q) * n)) := by
  have hroot : (kilianCommit H V k x table).length ≤ n :=
    ((length_merkleRoot (hlen k) _).trans hk).le
  have hchallenges : (ρs.map List.length).sum ≤ n * V.coins x := by
    refine (List.sum_le_length_nsmul _ (V.coins x) fun m hm => ?_).trans (by simp [hn])
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hm
    exact (hρs ρ hρ).le
  have hresponse : kilianResponseBits (kilianRespond H V k x table ρs) ≤
      n * (q * (1 + (V.coins x + Nat.clog 2 q) * n)) := by
    refine (kilianResponseBits_kilianRespond_le hlen hq hρs).trans ?_
    rw [hn, hk]
    gcongr
    exact kilianDepth_le hq
  unfold kilianCommunication
  linarith

/-- **Polylogarithmic communication**: for a verifier with at most `c * (log₂ |enc x| + 1)`
random bits and at most `q` queries per random string (as the verifier of the PCP theorem has, with
`q` constant), the honest transcript after the statement has at most
`(2 + c + q + q * c + q * ⌈log₂ q⌉) * (n + 1) ^ 2 * (log₂ |enc x| + 1)` bits. -/
theorem kilianCommunication_honest_le_log {enc : α ↪ List Bool} {c : ℕ}
    (hlen : ∀ k x, (H k x).length = k.length)
    {n : ℕ} {k : List Bool} (hk : k.length = n) {x : α} {table : List Bool}
    {ρs : List (List Bool)} (hn : ρs.length = n) (hρs : ∀ ρ ∈ ρs, ρ.length = V.coins x) {q : ℕ}
    (hq : ∀ ρ : List Bool, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ q)
    (hcoins : V.coins x ≤ c * (Nat.log 2 (enc x).length + 1)) :
    kilianCommunication k (kilianCommit H V k x table) ρs (kilianRespond H V k x table ρs) ≤
      (2 + c + q + q * c + q * Nat.clog 2 q) * (n + 1) ^ 2 * (Nat.log 2 (enc x).length + 1) := by
  set ℓ := Nat.log 2 (enc x).length + 1
  set L := Nat.clog 2 q
  have hℓ : 0 < ℓ := Nat.succ_pos _
  have hn1 : n ≤ (n + 1) ^ 2 := by nlinarith
  have hn2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left n.le_succ 2
  refine (kilianCommunication_honest_le hlen hk hn hρs hq).trans
    ((?_ : _ ≤ 2 * n + n * (c * ℓ) + n * (q * (1 + (c * ℓ + L) * n))).trans ?_)
  · gcongr
  · nlinarith [Nat.mul_le_mul_left q (hn1.trans (Nat.le_mul_of_pos_right _ hℓ)),
      Nat.mul_le_mul_left c (Nat.mul_le_mul_right ℓ hn1),
      Nat.mul_le_mul_left (q * c) (Nat.mul_le_mul_right ℓ hn2),
      Nat.mul_le_mul_left (q * L) (hn2.trans (Nat.le_mul_of_pos_right _ hℓ))]

/-! ### The verifier's input -/

/-- **The honest verifier input is short**: on an honest transcript at security parameter `n`, the
encoded input of `kilianVerify` (the input of `computableInPolyTime_kilianVerify`) has length at
most `4 * |enc x| + 6 * n + 6 + 2 * n * (2 * r + 1) + n * (2 * q * B + 1)` with
`B = 2 * (3 + (r + ⌈log₂ q⌉) * (2 * n + 1)) + 1`, linear in the statement and polynomial in `n`
and the PCP parameters. This is an input-length bound, not a runtime certificate. Combined with
`computableInPolyTime_kilianVerify` under its polynomial-time hash, digest-length, `V.PolyTime`
and logarithmic-randomness hypotheses, and a polynomial query bound (constant for the
PCP-theorem verifier), it gives polynomial time in `n + |enc x|` on honest transcripts. -/
theorem length_kilianVerifierInput_honest_le {enc : α ↪ List Bool}
    (hlen : ∀ k x, (H k x).length = k.length)
    {n : ℕ} {k : List Bool} (hk : k.length = n) {x : α} {table : List Bool}
    {ρs : List (List Bool)} (hn : ρs.length = n) (hρs : ∀ ρ ∈ ρs, ρ.length = V.coins x) {q : ℕ}
    (hq : ∀ ρ : List Bool, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ q) :
    (encKilianView enc
      { key := k, stmt := x, root := kilianCommit H V k x table, challenges := ρs,
        response := kilianRespond H V k x table ρs }).length ≤
      4 * (enc x).length + 6 * n + 6 + 2 * (n * (2 * V.coins x + 1)) +
        n * (2 * (q * (2 * (3 + (V.coins x + Nat.clog 2 q) * (2 * n + 1)) + 1)) + 1) := by
  set d := V.coins x + Nat.clog 2 q
  have hroot : (kilianCommit H V k x table).length ≤ n :=
    ((length_merkleRoot (hlen k) _).trans hk).le
  have hopening (ρ : List Bool) (o : MerkleOpening Bool) (ho : o ∈ kilianOpen H V k x table ρ) :
      (encKilianOpening o).length ≤ 3 + d * (2 * n + 1) := by
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp ho
    have hpath := length_encList_le encBits
      (merklePath H k (kilianLeaves (kilianTable V x table)) (kilianPosition V x a))
      (b := n) fun s hs => by simpa [hk] using length_le_of_mem_merklePath hlen hs
    have hdepth : (merklePath H k (kilianLeaves (kilianTable V x table))
        (kilianPosition V x a)).length ≤ d := by
      simpa [length_merklePath, kilianLeaves, kilianDepth] using kilianDepth_le hq
    simp only [encKilianOpening_apply, length_encPair, encBool_apply, List.length_singleton]
    nlinarith
  have hresponse : (encKilianResponse (kilianRespond H V k x table ρs)).length ≤
      n * (2 * (q * (2 * (3 + d * (2 * n + 1)) + 1)) + 1) := by
    refine (length_encList_le _ _ (b := q * (2 * (3 + d * (2 * n + 1)) + 1))
      fun answers h => ?_).trans (by simp [kilianRespond, hn])
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp h
    refine (length_encList_le _ _ (hopening ρ)).trans ?_
    simpa only [kilianOpen, List.length_map] using Nat.mul_le_mul_right _ (hq ρ (hρs ρ hρ))
  have hchallenges : (encList encBits ρs).length ≤ n * (2 * V.coins x + 1) :=
    (length_encList_le _ _ (b := V.coins x) fun ρ hρ => (hρs ρ hρ).le).trans (by rw [hn])
  enc_len [encKilianView_apply, encKilianClaim_apply, hk]

/-- **Honest-transcript verifier runtime and space**: under a polynomial-time hash with
key-length digests and a polynomial-time PCP verifier `V` using `O(log |enc x|)` coins and at most
`q` queries per random string, there is a fixed binary multi-tape Turing machine computing
`kilianVerify` on every `KilianView α` in polynomial time and space in the encoded view, whose step
and space bounds on every honest transcript at security parameter `n` are bounded by polynomially
bounded functions of `n + |enc x|`. -/
theorem computableInTimeAndSpace_kilianVerify_honest_le {enc : α ↪ List Bool} {c q : ℕ}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hq : ∀ x (ρ : List Bool), ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ q) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
      (t s tHonest sHonest : ℕ → ℕ),
      PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      PolynomiallyBounded tHonest ∧ PolynomiallyBounded sHonest ∧
      tm.ComputesFunInTimeAndSpace (encKilianView enc) encBool
        (fun v => kilianVerify H V v.key v.stmt v.root v.challenges v.response)
        (fun v => t (encKilianView enc v).length)
        (fun v => s (encKilianView enc v).length) ∧
      (∀ (n : ℕ) (key : List Bool) (x : α) (table : List Bool) (ρs : List (List Bool)),
        key.length = n → ρs.length = n → (∀ ρ ∈ ρs, ρ.length = V.coins x) →
          let view : KilianView α :=
            { key := key, stmt := x, root := kilianCommit H V key x table,
              challenges := ρs, response := kilianRespond H V key x table ρs }
          t (encKilianView enc view).length ≤ tHonest (n + (enc x).length) ∧
          s (encKilianView enc view).length ≤ sHonest (n + (enc x).length) ∧
          tm.ComputesInTimeAndSpace (encKilianView enc view)
            (encBool (kilianVerify H V key x view.root ρs view.response))
            (tHonest (n + (enc x).length)) (sHonest (n + (enc x).length))) := by
  let inBound : ℕ → ℕ := fun u =>
    4 * u + 6 * u + 6 + 2 * (u * (2 * (c * (u + 1)) + 1)) +
      u * (2 * (q * (2 * (3 + (c * (u + 1) + Nat.clog 2 q) * (2 * u + 1)) + 1)) + 1)
  obtain ⟨kTM, State, hfin, tm, t, s, tHonest, sHonest, ht_pb, hs_pb, htH, hsH, htm', hbound⟩ :=
    computableInTimeAndSpace_kilianVerify_of_bound hH hlen hV hcoins
      (fun v => ∃ n table, v.key.length = n ∧ v.challenges.length = n ∧
        (∀ ρ ∈ v.challenges, ρ.length = V.coins v.stmt) ∧
        v.root = kilianCommit H V v.key v.stmt table ∧
        v.response = kilianRespond H V v.key v.stmt table v.challenges)
      (fun v => v.key.length + (enc v.stmt).length) inBound (by dsimp only [inBound]; fun_prop)
      fun ⟨⟨k, stmt, root⟩, challenges, response⟩ ⟨n, table, hk, hn, hρs, hroot, hresp⟩ => by
        dsimp only at hk hn hρs hroot hresp ⊢
        subst hroot hresp
        have hcoins_le : V.coins stmt ≤ c * ((n + (enc stmt).length) + 1) :=
          (hcoins stmt).trans (Nat.mul_le_mul_left c (Nat.succ_le_succ
            ((Nat.log_le_self 2 _).trans (Nat.le_add_left _ _))))
        rw [hk]
        refine (length_kilianVerifierInput_honest_le hlen hk hn hρs (hq stmt)).trans ?_
        have hn_le : n ≤ n + (enc stmt).length := Nat.le_add_right _ _
        have hx_le : (enc stmt).length ≤ n + (enc stmt).length := Nat.le_add_left _ _
        dsimp only [inBound]
        gcongr
  refine ⟨kTM, State, hfin, tm, t, s, tHonest, sHonest, ht_pb, hs_pb, htH, hsH, htm',
    fun n key x table ρs hk hn hρs => ?_⟩
  simpa [hk] using hbound
    { key := key, stmt := x, root := kilianCommit H V key x table,
      challenges := ρs, response := kilianRespond H V key x table ρs }
    ⟨n, table, hk, hn, hρs, rfl, rfl⟩

end Cslib.Crypto
