/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Randomized
public import CslibFrontier.Computability.Streaming.Basic
import CslibFrontier.Probability.PMF.Event

/-!
# Multi-pass streaming algorithms give protocols

A deterministic **multi-pass streaming algorithm** (`Cslib.Streaming.MultiPass σ α β`) reads the
stream `s` several times from left to right. It is a one-pass algorithm
(`Cslib.Streaming.Algorithm`) whose memory state is kept from one pass to the next, with
`endPass` applied at the end of each pass, so that it can for instance count its passes; after `p`
passes it reports the output of its state (`Cslib.Streaming.MultiPass.run`). Its memory is
measured as for one pass: `A.SpaceLE p m b` says that the states it holds between items during
`p` passes over streams of at most `m` items have an injective `b`-bit encoding. The state after
`endPass` of the last pass is not counted: it is only used for the answer. A one-pass algorithm is
the case `p = 1` (`Cslib.Streaming.Algorithm.run_toMultiPass`,
`Cslib.Streaming.Algorithm.spaceLE_toMultiPass_iff`).

**Simulation.** For $p \ge 1$ passes, with the stream split as `u x ++ v y`, Alice runs each pass
on `u x` and sends the `b`-bit encoding of the memory state to Bob, who continues the pass on `v y`
and, except after the last pass, sends the encoding of the resulting state back
(`Cslib.Streaming.MultiPass.toProtocol`). This takes `p` messages from Alice and $p-1$ from Bob, so
if the answer on `u x ++ v y` determines `f x y`, then `f` has a deterministic protocol with
$(2p-1)b+1$ bits
(`Cslib.Streaming.MultiPass.ecomplexityFun_le_of_spaceLE`), and, for randomized multi-pass
algorithms with public randomness, a public-coin protocol with the same error
(`Cslib.Streaming.MultiPass.Randomized.ecomplexityFun_le_of_spaceLE`). This extends the one-pass
reduction of Alon, Matias and Szegedy [AlonMatiasSzegedy1999, Section 3]
(`CslibFrontier.Computability.Streaming.Communication`) to `p` passes. The `p`-pass simulation
itself is standard: Bar-Yossef, Jayram, Kumar and Sivakumar carry it out for several players
[BarYossefJayramKumarSivakumar2004, proof of Theorem 3.1], Chang and Kannan describe it with
$2p-1$ messages of at most $b$ bits each [ChangKannan2006, proof of Theorem 5.1], and Abboud,
Censor-Hillel, Khoury and Paz state it as a theorem, with the asymptotic bound
$pb = \Omega(\mathrm{CC}(f))$ [AbboudCensorHillelKhouryPaz2021, Theorem 14]. The exact constants
here are proved directly. Since later passes depend on
the whole stream, the whole stream `u x ++ v y` must have at most `m` items, whereas one pass only
needs this of `u x`; so for `p = 1` the one-pass theorem is slightly stronger.

## Main definitions

* `Cslib.Streaming.MultiPass`: deterministic multi-pass streaming algorithms, with
  `Cslib.Streaming.MultiPass.passes` and `Cslib.Streaming.MultiPass.run`.
* `Cslib.Streaming.MultiPass.reachable`, `Cslib.Streaming.MultiPass.SpaceLE`: the states reached
  during `p` passes, and memory bounds.
* `Cslib.Streaming.Algorithm.toMultiPass`: a one-pass algorithm as a multi-pass one.
* `Cslib.Streaming.MultiPass.toProtocol`: the protocol simulating `p` passes, for $p \ge 1$.
* `Cslib.Streaming.MultiPass.Randomized`, `Cslib.Streaming.MultiPass.Randomized.SpaceLE`:
  randomized multi-pass algorithms with public randomness, and their memory.

## Main results

* `Cslib.Streaming.Algorithm.spaceLE_toMultiPass_iff`: the memory of a one-pass algorithm is its
  memory as a multi-pass algorithm making one pass.
* `Cslib.Streaming.MultiPass.SpaceLE.mono`: memory bounds for longer streams and more passes give
  memory bounds for shorter streams and fewer passes.
* `Cslib.Streaming.MultiPass.depth_toProtocol_le`, `Cslib.Streaming.MultiPass.run_toProtocol`: the
  simulation of $p \ge 1$ passes sends $(2p-1)b+1$ bits and answers as the algorithm.
* `Cslib.Streaming.MultiPass.ecomplexityFun_le_of_spaceLE`,
  `Cslib.Streaming.MultiPass.Randomized.ecomplexityFun_le_of_spaceLE`: `p`-pass streaming memory
  bounds deterministic and public-coin communication, for $p \ge 1$.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Section 3][AlonMatiasSzegedy1999]
* [Z. Bar-Yossef, T. S. Jayram, R. Kumar, D. Sivakumar, *An information statistics approach to
  data stream and communication complexity*, proof of Theorem 3.1,
  pp. 708–709][BarYossefJayramKumarSivakumar2004]
* [K. L. Chang, R. Kannan, *The space complexity of pass-efficient algorithms for clustering*,
  proof of Theorem 5.1, p. 1165][ChangKannan2006]
* [A. Abboud, K. Censor-Hillel, S. Khoury, A. Paz, *Smaller cuts, higher lower bounds*,
  Theorem 14][AbboudCensorHillelKhouryPaz2021]
-/

public section

namespace Cslib.Streaming

/-- A deterministic **multi-pass streaming algorithm**: a one-pass algorithm whose memory state is
kept from one pass over the stream to the next, with `endPass` applied at the end of each pass. -/
structure MultiPass (σ α β : Type*) extends Algorithm σ α β where
  /-- The memory state at the start of the next pass, given the state at the end of a pass. -/
  endPass : σ → σ

namespace MultiPass

variable {σ α β : Type*} (A : MultiPass σ α β)

/-- The memory state after one pass over `s` from `q`, including `endPass`. -/
@[expose] def pass (s : List α) (q : σ) : σ :=
  A.endPass (A.stateFrom q s)

/-- The memory state after `k` passes over `s`. -/
@[expose] def passes (s : List α) (k : ℕ) : σ :=
  (A.pass s)^[k] A.init

/-- The answer after `p` passes over `s`. -/
@[expose] def run (p : ℕ) (s : List α) : β :=
  A.output (A.passes s p)

@[simp] theorem passes_zero (s : List α) : A.passes s 0 = A.init :=
  rfl

theorem passes_succ (s : List α) (k : ℕ) : A.passes s (k + 1) = A.pass s (A.passes s k) :=
  Function.iterate_succ_apply' _ _ _

/-- A pass over `s ++ t` is a pass over `s` continued on `t`. -/
theorem pass_append (s t : List α) (q : σ) :
    A.pass (s ++ t) q = A.endPass (A.stateFrom (A.stateFrom q s) t) := by
  rw [pass, A.stateFrom_append]

/-- The memory states reachable during `p` passes over streams of length at most `m`: the states
held between items during each pass, from its start to its end (before `endPass`). -/
@[expose] def reachable (p m : ℕ) : Set σ :=
  {q | ∃ s : List α, s.length ≤ m ∧ ∃ k < p, ∃ t, t <+: s ∧ A.stateFrom (A.passes s k) t = q}

/-- `A` **uses at most `b` bits of memory during `p` passes over streams of length at most `m`**:
the memory states it reaches have an injective encoding by `b`-bit strings. -/
@[expose] def SpaceLE (p m b : ℕ) : Prop :=
  ∃ enc : σ → BitString b, Set.InjOn enc (A.reachable p m)

theorem stateFrom_mem_reachable {p m k : ℕ} {s t : List α} (hs : s.length ≤ m) (hk : k < p)
    (ht : t <+: s) : A.stateFrom (A.passes s k) t ∈ A.reachable p m :=
  ⟨s, hs, k, hk, t, ht, rfl⟩

theorem passes_mem_reachable {p m k : ℕ} {s : List α} (hs : s.length ≤ m) (hk : k < p) :
    A.passes s k ∈ A.reachable p m :=
  A.stateFrom_mem_reachable hs hk List.nil_prefix

theorem reachable_mono {p p' m m' : ℕ} (hp : p ≤ p') (hm : m ≤ m') :
    A.reachable p m ⊆ A.reachable p' m' :=
  fun _ ⟨s, hs, k, hk, t, ht, hq⟩ => ⟨s, hs.trans hm, k, hk.trans_le hp, t, ht, hq⟩

variable {A} in
/-- Memory bounds for longer streams and more passes give memory bounds for shorter streams and
fewer passes. -/
theorem SpaceLE.mono {p p' m m' b : ℕ} (h : A.SpaceLE p' m' b) (hp : p ≤ p') (hm : m ≤ m') :
    A.SpaceLE p m b :=
  let ⟨enc, henc⟩ := h
  ⟨enc, henc.mono (A.reachable_mono hp hm)⟩

end MultiPass

namespace Algorithm

variable {σ α β : Type*} (A : Algorithm σ α β)

/-- A one-pass algorithm as a multi-pass algorithm that does nothing at the end of a pass. -/
@[expose] def toMultiPass : MultiPass σ α β :=
  { A with endPass := id }

/-- One pass of `A.toMultiPass` is a run of `A`. -/
@[simp] theorem run_toMultiPass (s : List α) : A.toMultiPass.run 1 s = A.run s :=
  rfl

/-- In one pass, `A.toMultiPass` reaches the states that `A` reaches. -/
theorem reachable_toMultiPass (m : ℕ) : A.toMultiPass.reachable 1 m = A.reachable m := by
  ext q
  constructor
  · rintro ⟨s, hs, k, hk, t, ht, rfl⟩
    obtain rfl : k = 0 := by omega
    exact ⟨t, ht.length_le.trans hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, 0, one_pos, s, List.prefix_rfl, rfl⟩

/-- `A.toMultiPass` uses `b` bits of memory in one pass exactly when `A` does. -/
theorem spaceLE_toMultiPass_iff {m b : ℕ} : A.toMultiPass.SpaceLE 1 m b ↔ A.SpaceLE m b := by
  rw [MultiPass.SpaceLE, Algorithm.SpaceLE, reachable_toMultiPass]

end Algorithm

namespace MultiPass

variable {σ α β X Y : Type*} (A : MultiPass σ α β)

open Communication

/-- Decoding a `b`-bit message: the state reachable during `p` passes over streams of length at
most `m` that `enc` maps to it, if any. -/
noncomputable def decode (p m b : ℕ) (enc : σ → BitString b) (w : BitString b) : σ :=
  haveI : Nonempty σ := ⟨A.init⟩
  Function.invFunOn enc (A.reachable p m) w

theorem decode_enc {p m b : ℕ} {enc : σ → BitString b} (henc : Set.InjOn enc (A.reachable p m))
    {q : σ} (hq : q ∈ A.reachable p m) : A.decode p m b enc (enc q) = q :=
  haveI : Nonempty σ := ⟨A.init⟩
  henc.leftInvOn_invFunOn hq

/-- The protocol simulating the last `n + 1` passes, starting from the state `q` that both players
know. Alice continues the pass from `q` on `u x` and sends the encoded state; Bob decodes it and
finishes the pass on `v y`. After the last pass Bob announces `d` of the answer; otherwise he sends
the encoded state, and the simulation continues from its decoding. -/
noncomputable def simFrom (p m b : ℕ) (enc : σ → BitString b) (u : X → List α) (v : Y → List α)
    (d : β → Bool) : ℕ → σ → Protocol X Y Bool
  | 0, q => Protocol.aliceSend b (fun x => enc (A.stateFrom q (u x))) fun w =>
      Protocol.bob (fun y => d (A.output (A.endPass (A.stateFrom (A.decode p m b enc w) (v y)))))
        (Protocol.output false) (Protocol.output true)
  | n + 1, q => Protocol.aliceSend b (fun x => enc (A.stateFrom q (u x))) fun w =>
      Protocol.bobSend b (fun y => enc (A.endPass (A.stateFrom (A.decode p m b enc w) (v y))))
        fun w' => simFrom p m b enc u v d n (A.decode p m b enc w')

/-- The protocol in which Alice and Bob simulate `p` passes of `A` over `u x ++ v y`, exchanging the
`b`-bit encoding of the memory state, and Bob announces `d` of the answer. This is meant for
$p \ge 1$, which `Cslib.Streaming.MultiPass.run_toProtocol` and
`Cslib.Streaming.MultiPass.depth_toProtocol_le` assume: for `p = 0` the truncated subtraction
`p - 1 = 0` makes it the protocol for one pass, so it does not simulate `A.run 0`. -/
noncomputable def toProtocol (p m b : ℕ) (enc : σ → BitString b) (u : X → List α)
    (v : Y → List α) (d : β → Bool) : Protocol X Y Bool :=
  A.simFrom p m b enc u v d (p - 1) A.init

theorem depth_simFrom_le (p m b : ℕ) (enc : σ → BitString b) (u : X → List α) (v : Y → List α)
    (d : β → Bool) (n : ℕ) (q : σ) :
    (A.simFrom p m b enc u v d n q).depth ≤ (2 * n + 1) * b + 1 := by
  induction n generalizing q with
  | zero =>
    exact (Protocol.depth_aliceSend_le (d := 1) fun _ => by simp).trans (le_of_eq (by ring))
  | succ n ih =>
    exact (Protocol.depth_aliceSend_le fun _ => Protocol.depth_bobSend_le fun _ => ih _).trans
      (le_of_eq (by ring))

/-- The simulation of `p` passes sends $(2p-1)b+1$ bits. -/
theorem depth_toProtocol_le {p : ℕ} (hp : 0 < p) (m b : ℕ) (enc : σ → BitString b)
    (u : X → List α) (v : Y → List α) (d : β → Bool) :
    (A.toProtocol p m b enc u v d).depth ≤ (2 * p - 1) * b + 1 := by
  have h := A.depth_simFrom_le p m b enc u v d (p - 1) A.init
  rwa [show 2 * (p - 1) + 1 = 2 * p - 1 by omega] at h

theorem run_simFrom {p m b : ℕ} {enc : σ → BitString b} (henc : Set.InjOn enc (A.reachable p m))
    (u : X → List α) (v : Y → List α) (d : β → Bool) {x : X} {y : Y}
    (hm : (u x ++ v y).length ≤ m) (n k : ℕ) (hnk : k + n + 1 ≤ p) :
    (A.simFrom p m b enc u v d n (A.passes (u x ++ v y) k)).run x y =
      d (A.output (A.passes (u x ++ v y) (k + n + 1))) := by
  induction n generalizing k with
  | zero =>
    rw [simFrom, Protocol.run_aliceSend, Protocol.run_bob,
      A.decode_enc henc (A.stateFrom_mem_reachable hm (by omega) (List.prefix_append _ _)),
      ← A.pass_append, ← A.passes_succ]
    cases d (A.output (A.passes (u x ++ v y) (k + 0 + 1))) <;> rfl
  | succ n ih =>
    rw [simFrom, Protocol.run_aliceSend, Protocol.run_bobSend,
      A.decode_enc henc (A.stateFrom_mem_reachable hm (by omega) (List.prefix_append _ _)),
      ← A.pass_append, ← A.passes_succ,
      A.decode_enc henc (A.passes_mem_reachable hm (by omega)), ih (k + 1) (by omega)]
    congr 3
    omega

/-- When `enc` is injective on the states reachable during `p` passes over streams of length at most
`m`, and the stream `u x ++ v y` has length at most `m`, the simulation answers as the algorithm. -/
theorem run_toProtocol {p m b : ℕ} (hp : 0 < p) {enc : σ → BitString b}
    (henc : Set.InjOn enc (A.reachable p m)) (u : X → List α) (v : Y → List α) (d : β → Bool)
    {x : X} {y : Y} (hm : (u x ++ v y).length ≤ m) :
    (A.toProtocol p m b enc u v d).run x y = d (A.run p (u x ++ v y)) := by
  have h := A.run_simFrom henc u v d hm (p - 1) 0 (by omega)
  rw [passes_zero, show 0 + (p - 1) + 1 = p by omega] at h
  exact h

/-- **Multi-pass streaming space bounds communication** (deterministic): if, for $p \ge 1$, a
`p`-pass streaming algorithm with `b` bits of memory on streams of length at most `m` decides
`f x y` from its answer on the stream `u x ++ v y`, which has length at most `m`, then `f` has a
deterministic protocol with $(2p-1)b+1$ bits. -/
theorem ecomplexityFun_le_of_spaceLE {p m b : ℕ} (hp : 0 < p) (hA : A.SpaceLE p m b)
    (u : X → List α) (v : Y → List α) (hm : ∀ x y, (u x ++ v y).length ≤ m) (d : β → Bool)
    (f : X → Y → Bool) (hf : ∀ x y, d (A.run p (u x ++ v y)) = f x y) :
    Protocol.ecomplexityFun f ≤ (2 * p - 1) * b + 1 := by
  obtain ⟨enc, henc⟩ := hA
  have := Protocol.ecomplexityFun_le_depth (p := A.toProtocol p m b enc u v d)
    (funext₂ fun x y => (A.run_toProtocol hp henc u v d (hm x y)).trans (hf x y))
  exact this.trans (by exact_mod_cast A.depth_toProtocol_le hp m b enc u v d)

/-! ### Randomized multi-pass algorithms -/

/-- A randomized multi-pass streaming algorithm with **public randomness**: a distribution over
deterministic ones. As for one pass (`Cslib.Streaming.Randomized`), the random choices are not
charged to the memory. -/
abbrev Randomized (σ α β : Type*) : Type _ :=
  PMF (MultiPass σ α β)

/-- Every algorithm that `μ` can draw uses at most `b` bits of memory during `p` passes over streams
of length at most `m`. -/
@[expose] def Randomized.SpaceLE (μ : Randomized σ α β) (p m b : ℕ) : Prop :=
  ∀ A ∈ μ.support, A.SpaceLE p m b

/-- **Multi-pass streaming space bounds communication** (public coins): if, for $p \ge 1$, a
randomized `p`-pass streaming algorithm `μ` whose algorithms use at most `b` bits of memory on
streams of length at most `m` decides `f x y` with error `ε` from its answer on `u x ++ v y`, which
has length at most `m`, then `f` has a public-coin protocol with error `ε` and $(2p-1)b+1$ bits. -/
theorem Randomized.ecomplexityFun_le_of_spaceLE (μ : Randomized σ α β) {p m b : ℕ} (hp : 0 < p)
    (hμ : μ.SpaceLE p m b) (u : X → List α) (v : Y → List α)
    (hm : ∀ x y, (u x ++ v y).length ≤ m) (d : β → Bool) (f : X → Y → Bool) {ε : ℝ}
    (hf : ∀ x y, (μ.toOuterMeasure {A | d (A.run p (u x ++ v y)) ≠ f x y}).toReal ≤ ε) :
    PublicCoin.ecomplexityFun ε f ≤ (2 * p - 1) * b + 1 := by
  classical
  let P : MultiPass σ α β → Protocol X Y Bool := fun A =>
    if h : A.SpaceLE p m b then A.toProtocol p m b h.choose u v d else Protocol.output false
  refine (PublicCoin.ecomplexity_le_depth (μ := μ.map P) fun x _ y _ => ?_).trans ?_
  · refine le_trans ?_ (hf x y)
    unfold PublicCoin.errorProb Probability.PMF.errorProb
    rw [PMF.toOuterMeasure_map_apply]
    refine ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
      (PMF.toOuterMeasure_mono _ ?_)
    rintro A ⟨hA, hsupp⟩
    have hs := hμ A hsupp
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, P, dite_eq_left hs] at hA ⊢
    rwa [A.run_toProtocol hp hs.choose_spec u v d (hm x y), eq_comm] at hA
  · refine Probability.PMF.maxCost_map_le_of_le Protocol.depth P μ fun A hA => ?_
    simp only [P, dite_eq_left (hμ A hA)]
    exact A.depth_toProtocol_le hp m b _ u v d

end MultiPass

end Cslib.Streaming
