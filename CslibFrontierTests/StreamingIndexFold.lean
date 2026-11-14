/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


import CslibFrontier.Computability.GenericRAM.Native.IndexFold
import Mathlib.Data.Nat.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming

/-! # Streaming binary-index fold controls

The range list appears only in specifications and these small tests. The implementation retains
one index and one accumulator. No finite, inhabited, or standard-encoding assumption is imposed
on the generic accumulator.
-/


open Cslib.GenericRAM Turing.MultiTapeTM
open Cslib.GenericRAM.IndexFold

-- The empty enumeration never evaluates its body, even when that body changes every state.
example : run (fun p : ℕ × ℕ => p.1 + p.2 + 100) 0 7 = (0, 7) := rfl

-- The body sees the OLD index, starting at zero, exactly once and in ascending order.
example : run (fun p : ℕ × List ℕ => p.2 ++ [p.1]) 5 [] =
    (5, [0, 1, 2, 3, 4]) := by decide

-- Carry across 7 to 8 does not skip or duplicate an index.
example : run (fun p : ℕ × ℕ => p.2 + p.1) 9 0 = (9, 36) := by decide

-- A noncommutative accumulator distinguishes the traversal from reversed traversal.
example : run (fun p : ℕ × ℕ => 10 * p.2 + p.1) 4 0 = (4, 123) := by decide

-- A single round calls index zero, rather than index one.
example : run (fun p : ℕ × ℕ => p.1) 1 99 = (1, 0) := rfl

-- Captured data can be retained in the accumulator and is not reconstructed from the index.
example : run (fun p : ℕ × (ℕ × List ℕ) =>
    (p.2.1, p.2.2 ++ [p.1 + p.2.1])) 3 (7, []) = (3, (7, [7, 8, 9])) := by decide

-- The prefix contract is fully generic, including infinite accumulator types.
example {β : Type} (body : ℕ × β → β) (initial : β) (n : ℕ) :
    run body n initial =
      (n, (List.range n).foldl (fun acc i => body (i, acc)) initial) :=
  run_eq body n initial

-- Arbitrary encodings and every reachable prefix, not only the final state.
example {β : Type} (enc : β ↪ List Bool) (body : ℕ × β → β) (initial : β)
    (n B : ℕ) (h : ∀ j ≤ n, (enc (run body j initial).2).length ≤ B) :
    ∀ j ≤ n, (encPair encNat enc (run body j initial)).length ≤
      2 * (encNat n).length + 1 + B := by
  intro j hj
  exact length_run_le body initial hj (h j hj)

-- Exponentially many visits can still retain only a linear-size binary index.
example {β : Type} (enc : β ↪ List Bool) (body : ℕ × β → β) (initial : β)
    (k j B : ℕ) (hj : j ≤ 2 ^ k) (h : (enc (run body j initial).2).length ≤ B) :
    (encPair encNat enc (run body j initial)).length ≤ 2 * (k + 1) + 1 + B := by
  have hb := length_run_le body initial hj h
  have hlen : (encNat (2 ^ k)).length = k + 1 := by
    change (2 ^ k).bits.length = k + 1
    rw [Nat.size_eq_bits_len, Nat.size_pow]
  rw [hlen] at hb
  exact hb

-- No native implementation of the body is inferred merely from its mathematical function.
example {α β : Type} {input : α ↪ List Bool} {enc : β ↪ List Bool}
    {n : α → ℕ} {initial : α → β} {_body : ℕ × β → β}
    (_cn : NativeCertificate n input encNat)
    (_ci : NativeCertificate initial input enc) : True := by
  fail_if_success
    have : IsComputable (fun a => run _body (n a) (initial a)) input
        (encPair encNat enc) := by
      exact (certificate _cn _ci (by assumption)).isComputable
  trivial

-- The native endpoint consumes the COMPLETE supplied callback certificate at its original
-- pair encoding. Count, initialization, callback and all runtime captured data remain generic.
example {α β : Type} {input : α ↪ List Bool} {enc : β ↪ List Bool}
    {n : α → ℕ} {initial : α → β} {body : ℕ × β → β}
    (cn : NativeCertificate n input encNat) (ci : NativeCertificate initial input enc)
    (cb : NativeCertificate body (encPair encNat enc) enc) :
    IsComputable (fun a => run body (n a) (initial a)) input (encPair encNat enc) :=
  (certificate cn ci cb).isComputable

-- A full-state bound cannot be inferred from a final-state bound alone.
example {β : Type} (enc : β ↪ List Bool) (body : ℕ × β → β) (initial : β)
    (n j B : ℕ) (_hj : j ≤ n) (_hfinal : (enc (run body n initial).2).length ≤ B) : True := by
  fail_if_success
    have : (encPair encNat enc (run body j initial)).length ≤
        2 * (encNat n).length + 1 + B := by
      exact length_run_le body initial _hj (by assumption)
  trivial

-- A real native callback, not a hypothesized efficient enumerator. Its full pair input is
-- charged, even though this particular callback only retains the Boolean accumulator.
private noncomputable def keepCertificate :
    NativeCertificate (fun p : ℕ × Bool => p.2) (encPair encNat encBool) encBool :=
  NativeCertificate.linear (ComputableInO.snd encNat encBool)

-- Binary carry has quadratic successor TIME and linear charged WORKSPACE, kept independent.
example : (roundCertificate keepCertificate).time (7, true) = 32 := by decide
example : (roundCertificate keepCertificate).space (7, true) = 20 := by decide

-- The final pair, not only its accumulator, is covered by the native output charge.
example : IsComputable (fun n : ℕ => run (fun p : ℕ × Bool => p.2) n true)
    encNat (encPair encNat encBool) := by
  exact (certificate (NativeCertificate.linear (ComputableInO.of_linear (.of_eq fun _ => rfl)))
    (NativeCertificate.const true) keepCertificate).isComputable

-- With a Boolean accumulator the live-state invariant is unconditional, even over 2^k visits.
example (body : ℕ × Bool → Bool) (k j : ℕ) (hj : j ≤ 2 ^ k) :
    (encPair encNat encBool (run body j true)).length ≤ 2 * (k + 1) + 2 := by
  have hb := length_run_le (encB := encBool) body true hj (B := 1) (by simp [encBool_apply])
  have hlen : (encNat (2 ^ k)).length = k + 1 := by
    change (2 ^ k).bits.length = k + 1
    rw [Nat.size_eq_bits_len, Nat.size_pow]
  rw [hlen] at hb
  simpa [Nat.add_assoc] using hb

-- Instantiate the independent resource theorem with an actual native callback, not assumed
-- prefix bounds. The Boolean value always occupies exactly one bit. R and Q charge the full
-- index/Boolean pair; the counted-loop theorem supplies its additional binary-counter costs.
example : ∃ T S, ComputableInO
    (fun n : ℕ => run (fun p : ℕ × Bool => p.2) n true)
    encNat (encPair encNat encBool) T S := by
  let cn := NativeCertificate.linear
    (ComputableInO.of_linear (.of_eq (encIn := encNat) (f := id) fun _ => rfl))
  let ci := NativeCertificate.const (ei := encNat) (em := encBool) true
  refine ⟨_, _, computableInO cn ci keepCertificate
    (fun n => 2 * (encNat n).length + 2)
    (fun n => 2 * (encNat n).length + 2) (fun _ => 1) ?_ ?_ ?_⟩
  · intro n j hj
    change (encPair encNat encBool (run (fun p => p.2) j true)).length ≤ _
    simpa [Nat.add_assoc] using length_run_le (encB := encBool) (fun p : ℕ × Bool => p.2) true hj
      (B := 1) (by simp [encBool_apply])
  · intro n j hj
    change (encPair encNat encBool (run (fun p => p.2) j true)).length ≤ _
    simpa [Nat.add_assoc] using length_run_le (encB := encBool) (fun p : ℕ × Bool => p.2) true hj
      (B := 1) (by simp [encBool_apply])
  · intro _ _ _
    simp [encBool_apply]

-- Independent callback time/workspace, arbitrary encoding, and exact cumulative contract.
example {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} (init : σ) {t s : σ × Bool → ℕ}
    (hstep : ComputableInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    {R : List Bool → ℕ → ℕ} {Q B : List Bool → ℕ}
    (hcost : ∀ l i (hi : i < l.length), t ((l.take i).foldl step init, l[i]) +
      (enc ((l.take i).foldl step init)).length +
      (enc ((l.take (i + 1)).foldl step init)).length + 1 ≤ R l i)
    (hspace : ∀ l i (hi : i < l.length), s ((l.take i).foldl step init, l[i]) ≤ Q l)
    (hstate : ∀ l i, i ≤ l.length → (enc ((l.take i).foldl step init)).length ≤ B l) :
    ∃ c, ComputableInTimeAndSpace (fun l => l.foldl step init) encBits enc
      (fun l => c * ((∑ i ∈ Finset.range l.length, R l i) + B l + 1))
      (fun l => c * (Q l + B l + 1)) :=
  hstep.foldl_bits_stream_sum init hcost hspace hstate

-- Independent callback time/workspace, arbitrary encoding, and exact cumulative contract.
example {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} {t s : σ × Bool → ℕ}
    (hstep : ComputableInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    (invariant : σ × List Bool → ℕ → σ → Prop)
    (hbase : ∀ p, invariant p 0 p.1)
    (hpreserve : ∀ p i (hi : i < p.2.length) state, invariant p i state →
      invariant p (i + 1) (step state p.2[i]))
    {R : σ × List Bool → ℕ → ℕ} {Q B : σ × List Bool → ℕ}
    (hcost : ∀ p i (hi : i < p.2.length) state, invariant p i state →
      t (state, p.2[i]) + (enc state).length + (enc (step state p.2[i])).length + 1 ≤ R p i ∧
        s (state, p.2[i]) ≤ Q p)
    (hsize : ∀ p i, i ≤ p.2.length → ∀ state, invariant p i state → (enc state).length ≤ B p) :
    (∃ c, ComputableInTimeAndSpace (fun p : σ × List Bool => p.2.foldl step p.1)
      (encPair enc encBits) enc
      (fun p => c * ((∑ i ∈ Finset.range p.2.length, R p i) + B p + 1))
      (fun p => c * (Q p + B p + 1))) ∧
      ∀ p, invariant p p.2.length (p.2.foldl step p.1) :=
  hstep.foldl_bits_pair_stream_sum_spec invariant hbase hpreserve hcost hsize

-- Independent callback time/workspace, arbitrary encoding, and exact cumulative contract.
example {σ : Type} {enc : σ ↪ List Bool}
    {f : σ → σ} {emit finish : σ → List Bool} {tN sN tE sE tF sF : σ → ℕ}
    (hnext : ComputableInTimeAndSpace f enc enc tN sN)
    (hemit : ComputableInTimeAndSpace emit enc encBits tE sE)
    (hfinish : ComputableInTimeAndSpace finish enc encBits tF sF)
    {R : σ × ℕ → ℕ → ℕ} {Q B : σ × ℕ → ℕ}
    (hcost : ∀ x i, i < x.2 → tN (f^[i] x.1) + tE (f^[i] x.1) + (enc (f^[i] x.1)).length +
      (enc (f^[i + 1] x.1)).length + 1 ≤ R x i)
    (hspace : ∀ x i, i < x.2 → sN (f^[i] x.1) + sE (f^[i] x.1) ≤ Q x)
    (hstate : ∀ x i, i ≤ x.2 → (enc (f^[i] x.1)).length ≤ B x) :
    ∃ c, ComputableInTimeAndSpace
      (fun x : σ × ℕ => ((List.range x.2).map fun i => emit (f^[i] x.1)).flatten ++
        finish (f^[x.2] x.1))
      (encPair enc encUnary) encBits
      (fun x => c * (tF (f^[x.2] x.1) + (∑ i ∈ Finset.range x.2, R x i) + B x + 1))
      (fun x => c * (sF (f^[x.2] x.1) + Q x + B x + 1)) :=
  hnext.iterate_unary_stream_sum hemit hfinish hcost hspace hstate

-- The empty stream retains the initial state; token order and state updates remain the pure fold.
example : ([] : List Bool).foldl (fun n b => 2 * n + if b then 1 else 0) 7 = 7 := rfl
example : [true, false, true].foldl (fun n b => 2 * n + if b then 1 else 0) 0 = 5 := by
  decide

-- Concrete paired callback: keep a captured bit and overwrite the last-seen bit. Overwrite
-- is noncommutative. The projection/pair providers supply the machine and its constants;
-- no exact clock for that composed machine is guessed here.
private def remember (s : Bool × Bool) (b : Bool) : Bool × Bool := (s.1, b)

private theorem remember_resources : ∃ K, ComputableInTimeAndSpace
    (fun p : (Bool × Bool) × Bool => remember p.1 p.2)
    (encPair (encPair encBool encBool) encBool) (encPair encBool encBool)
    (fun _ => K) (fun _ => K) := by
  have hc := ((ComputableInO.fst encBool encBool).comp_linear
    (ComputableInO.fst (encPair encBool encBool) encBool)).prod
    (ComputableInO.snd (encPair encBool encBool) encBool)
  obtain ⟨c, h, _⟩ := hc
  refine ⟨c * 32, h.mono ?_ ?_⟩ <;>
    intro p <;> simp only [length_encPair, encBool_apply, List.length_singleton] <;> omega

-- Discharge all resource and prefix premises, retaining the captured input at EVERY prefix.
-- The resulting space is constant even for an arbitrarily long stream.
example : ∃ K c, ComputableInTimeAndSpace
    (fun p : (Bool × Bool) × List Bool => p.2.foldl remember p.1)
    (encPair (encPair encBool encBool) encBits) (encPair encBool encBool)
    (fun p => c * (p.2.length * (K + 9) + 5)) (fun _ => c * (K + 5)) ∧
    ∀ p : (Bool × Bool) × List Bool, (p.2.foldl remember p.1).1 = p.1.1 := by
  obtain ⟨K, hk⟩ := remember_resources
  obtain ⟨⟨c, hc⟩, hs⟩ := hk.foldl_bits_pair_stream_sum_spec
    (fun p _ s => s.1 = p.1.1)
    (fun _ => rfl) (fun _ _ _ _ hs => hs)
    (R := fun _ _ => K + 9) (Q := fun _ => K) (B := fun _ => 4)
    (fun p i hi s hs => by
      constructor
      · simp [length_encPair, encBool_apply]
      · exact le_rfl)
    (fun p i hi s hs => by simp [length_encPair, encBool_apply])
  refine ⟨K, c, ?_, hs⟩
  simpa [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.add_assoc] using hc

-- These evaluate the SAME callback certified above, including the empty-stream boundary.
example (s : Bool × Bool) : ([] : List Bool).foldl remember s = s := rfl
example : [true, false].foldl remember (true, true) = (true, false) := rfl
example : [false, true].foldl remember (true, true) = (true, true) := rfl

-- A canonical map transducer copies a captured word with ZERO callback workspace.
-- Using the plain certificate exercises normalization in the streaming endpoint.
private theorem copyWord : ComputableInTimeAndSpace (id : List Bool → List Bool)
    encBits encBits (fun w => 4 * w.length + 8) (fun _ => 0) := by
  simpa using ComputableInTimeAndSpace.map_bits id

private def repeatedWord (x : List Bool × ℕ) : List Bool :=
  ((List.range x.2).map fun i => (id : List Bool → List Bool)^[i] x.1).flatten ++
    (id : List Bool → List Bool)^[x.2] x.1

-- Each round emits the whole captured word and retains only that word. Neither the callback
-- workspace nor the endpoint workspace bound contains the number of rounds or emitted length.
example : ∃ c, ComputableInTimeAndSpace repeatedWord (encPair encBits encUnary) encBits
    (fun x => c * (4 * x.1.length + 8 + x.2 * (10 * x.1.length + 17) + x.1.length + 1))
    (fun x => c * (x.1.length + 1)) := by
  obtain ⟨c, hc⟩ := copyWord.iterate_unary_stream_sum copyWord copyWord
    (R := fun x _ => 10 * x.1.length + 17) (Q := fun _ => 0)
    (B := fun x => x.1.length)
    (fun x i hi => by simp [encBits_apply] <;> omega)
    (fun x i hi => by omega)
    (fun x i hi => by simp [encBits_apply])
  refine ⟨c, ?_⟩
  simpa [repeatedWord, Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.add_assoc] using hc

-- Output really grows: the final callback emits once even when there are zero rounds.
example (w : List Bool) : repeatedWord (w, 0) = w := by simp [repeatedWord]
private theorem repeatedWord_length (w : List Bool) (n : ℕ) :
    (repeatedWord (w, n)).length = (n + 1) * w.length := by
  induction n with
  | zero => simp [repeatedWord]
  | succ n ih =>
    simp [repeatedWord, List.range_succ, List.map_append, List.flatten_append, Nat.add_mul] at ih ⊢
    omega

-- Zero-boundary controls use the provider's actual 8-step bound, never an invented zero clock.
example : (4 * ([] : List Bool).length + 8 : ℕ) = 8 := rfl
example (n : ℕ) : repeatedWord ([], n) = [] := by simp [repeatedWord]
example (n : ℕ) : (repeatedWord ([true], n)).length = n + 1 := by
  simpa using repeatedWord_length [true] n
