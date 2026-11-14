/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Complexity
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Decode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Machine
import CslibFrontier.Computability.Complexity.Classes.NP.Nondeterministic
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayVerdict
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.Nat.Bits

/-!
# NEXP-complete bounded nondeterministic acceptance

`Cslib.Complexity.NEXPBoundedAcceptance` [Arora and Barak, draft, Chapter 2 Exercises §9 and
Chapter 4 Exercises §3][AroraBarak07] is the set of instances `⟨α, x, T⟩`
(`Cslib.Complexity.NEXPBoundedAcceptanceInstance`), with `T` encoded in **binary** (`encNat`),
such that some certificate `c : List Bool` of length `|c| ≤ T` makes the machine described by `α`
accept `⟨x, c⟩ = encPair encBits encBits (x, c)` within `T` steps.

* **Membership in `NE` and `NEXP`** (`Cslib.Complexity.NEXPBoundedAcceptance.mem_NE`,
  `Cslib.Complexity.NEXPBoundedAcceptance.mem_NEXP`): a certificate `c` with `|c| ≤ T` is carried
  inside a fixed-length framed word `w` of length `2 * T + 1` via `unframe w = c` (padded with
  trailing `false` bits after `frame c`), and the deterministic verifier simulates the machine for
  `min |w| T` steps using `ComputableInPolyTime.binary_min_unary'`. Since `T < 2 ^ |enc a|`,
  `Cslib.Complexity.setOf_exists_mem_NTIME` places the language in `NE`, hence in `NEXP`.
* **`NE`- and `NEXP`-completeness** (`Cslib.Complexity.NEXPBoundedAcceptance.polyTimeComplete_NE`,
  `Cslib.Complexity.NEXPBoundedAcceptance.polyTimeComplete_NEXP`): every language in
  `NTIME enc (fun n => 2 ^ p n)` for a polynomial-time unary bound `p` reduces to
  `NEXPBoundedAcceptance` in polynomial time
  (`Cslib.Complexity.NEXPBoundedAcceptance.polyTimeReducible`) by compiling the nondeterministic
  decider's choice verifier `ntm.checkChoices encBits` into a deterministic linear-time machine and
  setting `T = 2 ^ (p |enc a| + |enc a| + C)`.
* **`NEXP = EXP` collapse criterion**
  (`Cslib.Complexity.NEXPBoundedAcceptance.NEXP_eq_EXP_of_mem_EXP`,
  `Cslib.Complexity.NEXPBoundedAcceptance.NEXP_eq_EXP_iff`): if `NEXPBoundedAcceptance` belongs to
  `EXP`, then `NEXP = EXP` for every instance encoding.

## Main definitions

* `Cslib.Complexity.NEXPBoundedAcceptanceInstance`: instances `⟨α, x, T⟩` with binary `T`.
* `Cslib.Complexity.encNEXPBoundedAcceptanceInstance`: their structured tuple encoding.
* `Cslib.Complexity.NEXPBoundedAcceptanceInstance.decoder`: total polynomial-time decoder for
  `encNEXPBoundedAcceptanceInstance`.
* `Cslib.Complexity.NEXPBoundedAcceptanceInstance.Accepts`: acceptance of a certificate `c` within
  `a.steps` steps.
* `Cslib.Complexity.NEXPBoundedAcceptance`: the language `{⟨α, x, T⟩ | ∃ c, |c| ≤ T ∧ Accepts c}`.
* `Cslib.Complexity.NEXPBoundedAcceptance.verifier`: polynomial-time verifier on framed certificates
  with step budget `min |w| T`.

## Main results

* `Cslib.Complexity.NEXPBoundedAcceptanceInstance.accepts_desc_iff`: acceptance on the description
  of a machine.
* `Cslib.Complexity.NEXPBoundedAcceptance.mem_NE`,
  `Cslib.Complexity.NEXPBoundedAcceptance.mem_NEXP`: membership in `NE` and `NEXP`.
* `Cslib.Complexity.NEXPBoundedAcceptance.polyTimeReducible`: reduction from
  `NTIME enc (fun n => 2 ^ p n)` for polynomial-time `p`.
* `Cslib.Complexity.NEXPBoundedAcceptance.polyTimeHard_NE`,
  `Cslib.Complexity.NEXPBoundedAcceptance.polyTimeHard_NEXP`,
  `Cslib.Complexity.NEXPBoundedAcceptance.polyTimeComplete_NE`,
  `Cslib.Complexity.NEXPBoundedAcceptance.polyTimeComplete_NEXP`: hardness and completeness for
  `NE` and `NEXP`.
* `Cslib.Complexity.NEXPBoundedAcceptance.NEXP_eq_EXP_of_mem_EXP`,
  `Cslib.Complexity.NEXPBoundedAcceptance.NEXP_eq_EXP_iff`: collapse of `NEXP` to `EXP` from
  deterministic exponential-time membership.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007][AroraBarak07]
-/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

public section

namespace Cslib.Complexity

/-- An instance `⟨α, x, T⟩` of `Cslib.Complexity.NEXPBoundedAcceptance`
[Arora and Barak, draft, Chapter 2 Exercises §9 and Chapter 4 Exercises §3][AroraBarak07], with the
step and certificate-length bound `T` encoded in binary. -/
structure NEXPBoundedAcceptanceInstance where
  /-- The description `α` of the machine. -/
  machine : Desc
  /-- The input `x`. -/
  input : List Bool
  /-- The step and certificate-length bound `T` (encoded in binary). -/
  steps : ℕ

/-- Encoding of `NEXPBoundedAcceptanceInstance` as the tuple of the machine description (`eDesc`),
the input bits (`encBits`), and the step bound in binary (`encNat`). -/
enc_structure encNEXPBoundedAcceptanceInstance : NEXPBoundedAcceptanceInstance where
  machine : eDesc,
  input : encBits,
  steps : encNat

attribute [fun_prop] encNEXPBoundedAcceptanceInstance_machine_polyTime
  encNEXPBoundedAcceptanceInstance_input_polyTime
  encNEXPBoundedAcceptanceInstance_steps_polyTime
  encNEXPBoundedAcceptanceInstance_mk_polyTime
  encNEXPBoundedAcceptanceInstance_steps_inO

namespace NEXPBoundedAcceptanceInstance

/-- Total decoder for `encNEXPBoundedAcceptanceInstance`. -/
def decoder : Decoder encNEXPBoundedAcceptanceInstance :=
  (Decoder.pair descDecoder (.pair .bits .nat)).map
    (fun ⟨m, x, s⟩ => ⟨m, x, s⟩) (fun a => (a.machine, a.input, a.steps))
    (fun _ => rfl) (fun _ => rfl)

/-- The certificate `c` makes the machine of `a` accept `⟨a.input, c⟩ = frame a.input ++ c` within
`a.steps` steps: run by the universal interpreter for `a.steps` steps, it has halted with the
output `[true]`. -/
@[expose] def Accepts (a : NEXPBoundedAcceptanceInstance) (c : List Bool) : Prop :=
  universal (a.machine, (encPair encBits encBits (a.input, c)).map eBit, a.steps) =
    ([eBit true], true)

noncomputable instance (a : NEXPBoundedAcceptanceInstance) (c : List Bool) :
    Decidable (a.Accepts c) :=
  inferInstanceAs (Decidable
    (universal (a.machine, (encPair encBits encBits (a.input, c)).map eBit, a.steps) =
      ([eBit true], true)))

theorem accepts_iff (a : NEXPBoundedAcceptanceInstance) (c : List Bool) :
    a.Accepts c ↔
      universal (a.machine, (encPair encBits encBits (a.input, c)).map eBit, a.steps) =
        ([eBit true], true) :=
  Iff.rfl

/-- **Acceptance on the description of a machine**: the machine, run on `⟨x, c⟩` for `T` steps,
has halted with output `[true]`. -/
theorem accepts_desc_iff {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (x : List Bool) (T : ℕ) (c : List Bool) :
    (⟨desc eS eBit tm, x, T⟩ : NEXPBoundedAcceptanceInstance).Accepts c ↔
      (tm.runFrom (tm.initCfg (encPair encBits encBits (x, c))) T).Halted ∧
        (tm.runFrom (tm.initCfg (encPair encBits encBits (x, c))) T).output = [true] := by
  rw [Accepts, universal_desc, Prod.mk.injEq, Cfg.Halted, Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨hout, hhalt⟩
    exact ⟨hhalt, List.map_injective_iff.mpr eBit.injective (hout.trans List.map_singleton.symm)⟩
  · rintro ⟨hhalt, hout⟩
    exact ⟨by rw [hout, List.map_singleton], hhalt⟩

end NEXPBoundedAcceptanceInstance

/-- **Bounded nondeterministic acceptance with a binary time bound**
[Arora and Barak, draft, Chapter 2 Exercises §9 and Chapter 4 Exercises §3][AroraBarak07]:
the instances `⟨α, x, T⟩` for which some certificate `c : List Bool` of length `|c| ≤ T` makes the
machine described by `α` accept `⟨x, c⟩` within `T` steps. -/
def NEXPBoundedAcceptance : Set NEXPBoundedAcceptanceInstance :=
  {a | ∃ c : List Bool, c.length ≤ a.steps ∧ a.Accepts c}

namespace NEXPBoundedAcceptance

theorem mem_iff {a : NEXPBoundedAcceptanceInstance} :
    a ∈ NEXPBoundedAcceptance ↔ ∃ c : List Bool, c.length ≤ a.steps ∧ a.Accepts c :=
  Iff.rfl

/-! ### Membership in `NE` and `NEXP` -/

/-- The framed-certificate verifier for `NEXPBoundedAcceptance`: decode `c = unframe w` from the
certificate word `w` and simulate `a.machine` on `⟨a.input, unframe w⟩` for `min |w| a.steps`
steps. When `|w| = 2 * a.steps + 1`, `min |w| a.steps = a.steps` and `unframe` ranges over all
words `c` of length at most `a.steps`. -/
noncomputable def verifier (q : NEXPBoundedAcceptanceInstance × List Bool) : Bool :=
  decide (universal (q.1.machine, (encPair encBits encBits (q.1.input, unframe q.2)).map eBit,
    min q.2.length q.1.steps) = ([eBit true], true))

theorem verifier_eq_true_iff (q : NEXPBoundedAcceptanceInstance × List Bool) :
    verifier q = true ↔
      universal (q.1.machine, (encPair encBits encBits (q.1.input, unframe q.2)).map eBit,
        min q.2.length q.1.steps) = ([eBit true], true) := by
  rw [verifier, decide_eq_true_iff]

/-- Doubling the length of `unframe w` never exceeds the length of `w`. -/
private theorem two_mul_length_unframe_le : ∀ w : List Bool, 2 * (unframe w).length ≤ w.length
  | [] | [true] => by simp [unframe]
  | false :: w => by simp [unframe]
  | true :: b :: w => by
    have := two_mul_length_unframe_le w
    simp only [unframe, List.length_cons]
    omega

/-- An instance `a` belongs to `NEXPBoundedAcceptance` iff some framed certificate `w` of exact
length `2 * a.steps + 1` satisfies `verifier (a, w) = true`. -/
theorem mem_iff_exists_verifier (a : NEXPBoundedAcceptanceInstance) :
    a ∈ NEXPBoundedAcceptance ↔
      ∃ w : List Bool, w.length = 2 * a.steps + 1 ∧ verifier (a, w) = true := by
  rw [mem_iff]
  constructor
  · rintro ⟨c, hc, hacc⟩
    refine ⟨frame c ++ List.replicate (2 * a.steps - 2 * c.length) false, ?_, ?_⟩
    · rw [List.length_append, length_frame, List.length_replicate]
      omega
    · rw [verifier_eq_true_iff]
      dsimp only
      rw [unframe_frame_append, List.length_append, length_frame,
        List.length_replicate, Nat.min_eq_right (by omega)]
      exact hacc
  · rintro ⟨w, hw, hV⟩
    rw [verifier_eq_true_iff] at hV
    dsimp only at hV
    rw [hw, Nat.min_eq_right (by omega)] at hV
    have hlen := two_mul_length_unframe_le w
    exact ⟨unframe w, by omega, hV⟩

/-- `NEXPBoundedAcceptance.verifier` is computable in polynomial time because `min |w| a.steps` is
computed in unary in polynomial time from the unary length `|w|` and the binary bound `a.steps`. -/
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encNEXPBoundedAcceptanceInstance encBits) encBool := by
  have hpair : ComputableInPolyTime (fun p : List Bool × List Bool => encPair encBits encBits p)
      (encPair encBits encBits) encBits :=
    .of_eq fun _ => rfl
  have hinput : ComputableInPolyTime
      (fun q : NEXPBoundedAcceptanceInstance × List Bool =>
        (encPair encBits encBits (q.1.input, unframe q.2)).map eBit)
      (encPair encNEXPBoundedAcceptanceInstance encBits) (encList encUnary) := by
    have hin : ComputableInPolyTime
        (fun q : NEXPBoundedAcceptanceInstance × List Bool =>
          encPair encBits encBits (q.1.input, unframe q.2))
        (encPair encNEXPBoundedAcceptanceInstance encBits) encBits :=
      hpair.comp ((encNEXPBoundedAcceptanceInstance_input_polyTime (.fst _ _)).prod
        (ComputableInPolyTime.unframe.comp (.snd _ _)))
    exact computableInPolyTime_map_eBit.comp hin
  have hmin : ComputableInPolyTime
      (fun q : NEXPBoundedAcceptanceInstance × List Bool => min q.2.length q.1.steps)
      (encPair encNEXPBoundedAcceptanceInstance encBits) encUnary :=
    ComputableInPolyTime.binary_min_unary'
      (ComputableInPolyTime.length_bits.comp (.snd _ _))
      (encNEXPBoundedAcceptanceInstance_steps_polyTime (.fst _ _))
  have huniv : ComputableInPolyTime
      (fun q : NEXPBoundedAcceptanceInstance × List Bool =>
        (q.1.machine, (encPair encBits encBits (q.1.input, unframe q.2)).map eBit,
          min q.2.length q.1.steps))
      (encPair encNEXPBoundedAcceptanceInstance encBits) eInUnary :=
    (encNEXPBoundedAcceptanceInstance_machine_polyTime (.fst _ _)).prod (hinput.prod hmin)
  exact (computableInPolyTime_universal.comp huniv).decide_eq' (.const _)

/-- The binary step bound `a.steps` is strictly below `2 ^ |enc a|`. -/
theorem steps_lt_two_pow_length (a : NEXPBoundedAcceptanceInstance) :
    a.steps < 2 ^ (encNEXPBoundedAcceptanceInstance a).length := by
  have hlt : a.steps < 2 ^ a.steps.bits.length :=
    Nat.size_eq_bits_len a.steps ▸ Nat.lt_size_self a.steps
  have hle : a.steps.bits.length ≤ (encNEXPBoundedAcceptanceInstance a).length :=
    encNEXPBoundedAcceptanceInstance_steps_length_le a
  exact hlt.trans_le (Nat.pow_le_pow_right (by omega) hle)

/-- **`NEXPBoundedAcceptance` is in `NE`.** -/
theorem mem_NE : NEXPBoundedAcceptance ∈ NE encNEXPBoundedAcceptanceInstance := by
  rw [NE, Set.mem_iUnion]
  have hcert : ComputableInPolyTime
      (fun a : NEXPBoundedAcceptanceInstance => 2 * a.steps + 1)
      encNEXPBoundedAcceptanceInstance encNat := by
    fun_prop
  obtain ⟨dC, _, hcert_deg⟩ := hcert.exists_degree
  have hℓ := ComputableInO.comp ComputableInO.natToUnary hcert_deg.inO
  obtain ⟨dV, _, hV_deg⟩ := computableInPolyTime_verifier.exists_degree
  have hV := hV_deg.inO
  let k := dC + dV + 1
  refine ⟨k, ?_⟩
  have hset : NEXPBoundedAcceptance =
      {a | ∃ w : List Bool, w.length = 2 * a.steps + 1 ∧ verifier (a, w) = true} :=
    Set.ext mem_iff_exists_verifier
  rw [hset]
  refine setOf_exists_mem_NTIME (t := fun n => 2 ^ (k * n)) hℓ hV (C := 5 + 4 ^ dV) fun a w hw => ?_
  set n := (encNEXPBoundedAcceptanceInstance a).length
  have hsteps : a.steps < 2 ^ n := steps_lt_two_pow_length a
  have hn1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have hk1 : 2 ^ n ≤ 2 ^ (k * n) :=
    Nat.pow_le_pow_right (by omega) (by dsimp [k]; nlinarith)
  have hdC : (n + 1) ^ dC ≤ 2 ^ (k * n) := by
    calc (n + 1) ^ dC
      _ ≤ (2 ^ n) ^ dC := Nat.pow_le_pow_left hn1 dC
      _ = 2 ^ (n * dC) := (Nat.pow_mul 2 n dC).symm
      _ ≤ 2 ^ (k * n) := Nat.pow_le_pow_right (by omega) (by dsimp [k]; nlinarith)
  have hpair_le : (encPair encNEXPBoundedAcceptanceInstance encBits (a, w)).length + 1 ≤
      4 * 2 ^ n := by
    rw [length_encPair]
    simp only [encBits, Function.Embedding.refl_apply, hw]
    change 2 * n + 1 + (2 * a.steps + 1) + 1 ≤ 4 * 2 ^ n
    omega
  have hdV : ((encPair encNEXPBoundedAcceptanceInstance encBits (a, w)).length + 1) ^ dV ≤
      4 ^ dV * 2 ^ (k * n) := by
    calc ((encPair encNEXPBoundedAcceptanceInstance encBits (a, w)).length + 1) ^ dV
      _ ≤ (4 * 2 ^ n) ^ dV := Nat.pow_le_pow_left hpair_le dV
      _ = 4 ^ dV * (2 ^ n) ^ dV := Nat.mul_pow 4 (2 ^ n) dV
      _ = 4 ^ dV * 2 ^ (n * dV) := by rw [← Nat.pow_mul]
      _ ≤ 4 ^ dV * 2 ^ (k * n) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by dsimp [k]; nlinarith))
  change n + ((n + 1) ^ dC + (2 * a.steps + 1)) +
    ((encPair encNEXPBoundedAcceptanceInstance encBits (a, w)).length + 1) ^ dV ≤
    (5 + 4 ^ dV) * 2 ^ (k * n) + (5 + 4 ^ dV)
  calc n + ((n + 1) ^ dC + (2 * a.steps + 1)) +
      ((encPair encNEXPBoundedAcceptanceInstance encBits (a, w)).length + 1) ^ dV
    _ ≤ 2 ^ (k * n) + (2 ^ (k * n) + 2 * 2 ^ (k * n)) + 4 ^ dV * 2 ^ (k * n) :=
      Nat.add_le_add (by omega) hdV
    _ = (4 + 4 ^ dV) * 2 ^ (k * n) := by ring
    _ ≤ (5 + 4 ^ dV) * 2 ^ (k * n) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ (5 + 4 ^ dV) * 2 ^ (k * n) + (5 + 4 ^ dV) := Nat.le_add_right _ _

/-- **`NEXPBoundedAcceptance` is in `NEXP`.** -/
theorem mem_NEXP : NEXPBoundedAcceptance ∈ NEXP encNEXPBoundedAcceptanceInstance :=
  NE_subset_NEXP mem_NE

/-! ### Hardness and completeness for `NE` and `NEXP` -/

/-- **Nondeterministic exponential-time problems reduce to `NEXPBoundedAcceptance`.**
Every language in `NTIME enc (fun n => 2 ^ p n)` for a polynomial-time unary function `p` reduces
to `NEXPBoundedAcceptance` in polynomial time. -/
theorem polyTimeReducible {α : Type} {enc : α ↪ List Bool} {A : Set α} {p : ℕ → ℕ}
    (hp : ComputableInPolyTime p encUnary encUnary)
    (hA : A ∈ NTIME enc (fun n => 2 ^ p n)) :
    PolyTimeReducible enc encNEXPBoundedAcceptanceInstance A NEXPBoundedAcceptance := by
  obtain ⟨c₁, c₂, k, State, hfinite, ntm, hdec⟩ := hA
  have := Fintype.ofFinite State
  obtain ⟨cV, ⟨kV, StateV, hfinV, tm, htm⟩, -⟩ :=
    MultiTapePTM.computableInO_decide_runClosedCoins ntm.choiceTable
  have := Fintype.ofFinite StateV
  let eSV : StateV ↪ ℕ := (Fintype.equivFin StateV).toEmbedding.trans Fin.valEmbedding
  let M := Nat.card (Turing.Action k Bool State)
  let C := (cV + 1) * (M + 1) * (c₁ + c₂ + 4)
  let stepBound (a : α) : ℕ := 2 ^ (p (enc a).length + (enc a).length + C)
  let tV (q : List Bool × List Bool) : ℕ := cV * ((encPair encBits encBits q).length + 1)
  have htV (q : List Bool × List Bool) :
      tV q ≤ cV * ((encPair encBits encBits q).length + 1) := le_rfl
  refine ⟨fun a => ⟨desc eSV eBit tm, enc a, stepBound a⟩, ?_, fun a => ?_⟩
  · have henc : ComputableInPolyTime (fun a => enc a) enc encBits := .of_eq fun _ => rfl
    have hlen : ComputableInPolyTime (fun a => (enc a).length) enc encUnary := by fun_prop
    have hp_comp : ComputableInPolyTime (fun a => p (enc a).length) enc encUnary := hp.comp hlen
    have hexp : ComputableInPolyTime (fun a => p (enc a).length + (enc a).length + C)
        enc encUnary := by fun_prop
    have hsteps : ComputableInPolyTime stepBound enc encNat :=
      ComputableInPolyTime.binary_two_pow.comp hexp
    fun_prop
  · rw [mem_iff]
    constructor
    · intro ha
      obtain ⟨c, hc_len, hc_acc⟩ :=
        (hdec.mem_iff_exists_checkChoices (a := a)
          (L := M * (c₁ * 2 ^ p (enc a).length + c₂)) le_rfl).mp ha
      have hpow_pos : 1 ≤ 2 ^ (p (enc a).length + (enc a).length) := Nat.one_le_two_pow
      have hpow_p : 2 ^ p (enc a).length ≤ 2 ^ (p (enc a).length + (enc a).length) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hn_le : (enc a).length ≤ 2 ^ (p (enc a).length + (enc a).length) :=
        Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by omega) (by omega))
      have hC_pow : C ≤ 2 ^ C := Nat.lt_two_pow_self.le
      have h1 : c₁ * 2 ^ p (enc a).length + c₂ ≤
          (c₁ + c₂) * 2 ^ (p (enc a).length + (enc a).length) := by
        calc c₁ * 2 ^ p (enc a).length + c₂
          _ ≤ c₁ * 2 ^ (p (enc a).length + (enc a).length) +
              c₂ * 2 ^ (p (enc a).length + (enc a).length) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hpow_p) (Nat.le_mul_of_pos_right _ hpow_pos)
          _ = (c₁ + c₂) * 2 ^ (p (enc a).length + (enc a).length) := by ring
      have hc_le_M : c.length ≤ M * (c₁ + c₂) * 2 ^ (p (enc a).length + (enc a).length) := by
        calc c.length
          _ = M * (c₁ * 2 ^ p (enc a).length + c₂) := hc_len
          _ ≤ M * ((c₁ + c₂) * 2 ^ (p (enc a).length + (enc a).length)) :=
            Nat.mul_le_mul_left M h1
          _ = M * (c₁ + c₂) * 2 ^ (p (enc a).length + (enc a).length) := by ring
      have hM_le_C : M * (c₁ + c₂) ≤ C := by
        have hM1 : M * (c₁ + c₂) ≤ (M + 1) * (c₁ + c₂ + 4) :=
          Nat.mul_le_mul (by omega) (by omega)
        calc M * (c₁ + c₂)
          _ ≤ 1 * ((M + 1) * (c₁ + c₂ + 4)) := by omega
          _ ≤ (cV + 1) * ((M + 1) * (c₁ + c₂ + 4)) :=
            Nat.mul_le_mul_right _ (by omega)
          _ = C := by ring
      have hc_step : c.length ≤ stepBound a := by
        calc c.length
          _ ≤ M * (c₁ + c₂) * 2 ^ (p (enc a).length + (enc a).length) := hc_le_M
          _ ≤ C * 2 ^ (p (enc a).length + (enc a).length) :=
            Nat.mul_le_mul_right _ hM_le_C
          _ ≤ 2 ^ C * 2 ^ (p (enc a).length + (enc a).length) :=
            Nat.mul_le_mul_right _ hC_pow
          _ = stepBound a := by rw [← Nat.pow_add, Nat.add_comm C]
      have htV_step : tV (enc a, c) ≤ stepBound a := by
        have hlen_pair : (encPair encBits encBits (enc a, c)).length + 1 =
            2 * (enc a).length + c.length + 2 := by
          simp only [length_encPair, encBits, Function.Embedding.refl_apply]
          omega
        have h2 : 2 * (enc a).length + c.length + 2 ≤
            (M + 1) * (c₁ + c₂ + 4) * 2 ^ (p (enc a).length + (enc a).length) := by
          have : 4 + M * (c₁ + c₂) ≤ (M + 1) * (c₁ + c₂ + 4) := by nlinarith
          nlinarith
        have htV_bound : tV (enc a, c) ≤ C * 2 ^ (p (enc a).length + (enc a).length) := by
          calc tV (enc a, c)
            _ ≤ cV * ((encPair encBits encBits (enc a, c)).length + 1) := htV (enc a, c)
            _ = cV * (2 * (enc a).length + c.length + 2) := by rw [hlen_pair]
            _ ≤ (cV + 1) * ((M + 1) * (c₁ + c₂ + 4) *
                  2 ^ (p (enc a).length + (enc a).length)) :=
              Nat.mul_le_mul (by omega) h2
            _ = C * 2 ^ (p (enc a).length + (enc a).length) := by ring
        calc tV (enc a, c)
          _ ≤ C * 2 ^ (p (enc a).length + (enc a).length) := htV_bound
          _ ≤ 2 ^ C * 2 ^ (p (enc a).length + (enc a).length) :=
            Nat.mul_le_mul_right _ hC_pow
          _ = stepBound a := by rw [← Nat.pow_add, Nat.add_comm C]
      obtain ⟨hhalt, hout⟩ := (htm (enc a, c)).runFrom_of_le htV_step
      change (tm.runFrom (tm.initCfg (encPair encBits encBits (enc a, c))) (stepBound a)).output =
        [ntm.checkChoices encBits (enc a, c)] at hout
      have hcheck : ntm.checkChoices encBits (enc a, c) = true := hc_acc
      refine ⟨c, hc_step, ?_⟩
      rw [NEXPBoundedAcceptanceInstance.accepts_desc_iff, hout, hcheck]
      exact ⟨hhalt, rfl⟩
    · rintro ⟨c, -, hacc⟩
      rw [NEXPBoundedAcceptanceInstance.accepts_desc_iff] at hacc
      rcases hacc with ⟨hhalt, hout⟩
      let T' := max (stepBound a) (tV (enc a, c))
      have hrun_eq := tm.runFrom_eq_of_halt _ (Nat.le_max_left (stepBound a) (tV (enc a, c))) hhalt
      obtain ⟨-, hout'⟩ := (htm (enc a, c)).runFrom_of_le (Nat.le_max_right (stepBound a) _)
      change (tm.runFrom (tm.initCfg (encPair encBits encBits (enc a, c))) T').output =
        [ntm.checkChoices encBits (enc a, c)] at hout'
      rw [hrun_eq, hout, List.singleton_inj] at hout'
      have hcheck : ntm.choiceTable.runClosedCoins c (enc a) = [true] :=
        of_decide_eq_true hout'.symm
      exact (hdec a).2.mpr (ntm.accepts_of_runClosedCoins_choiceTable hcheck)

/-- **`NEXPBoundedAcceptance` is hard for `NE`** under polynomial-time many-one reductions. -/
theorem polyTimeHard_NE : PolyTimeHard @NE encNEXPBoundedAcceptanceInstance NEXPBoundedAcceptance :=
  fun _ _ _ hA =>
    let ⟨k, hk⟩ := Set.mem_iUnion.mp hA
    polyTimeReducible (p := fun n => k * n) (by fun_prop) hk

/-- **`NEXPBoundedAcceptance` is hard for `NEXP`** under polynomial-time many-one reductions. -/
theorem polyTimeHard_NEXP :
    PolyTimeHard @NEXP encNEXPBoundedAcceptanceInstance NEXPBoundedAcceptance :=
  fun _ _ _ hA =>
    let ⟨k, hk⟩ := Set.mem_iUnion.mp hA
    polyTimeReducible (p := fun n => n ^ k) (by fun_prop) hk

/-- **`NEXPBoundedAcceptance` is `NE`-complete** under polynomial-time many-one reductions. -/
theorem polyTimeComplete_NE :
    PolyTimeComplete @NE encNEXPBoundedAcceptanceInstance NEXPBoundedAcceptance :=
  ⟨mem_NE, polyTimeHard_NE⟩

/-- **`NEXPBoundedAcceptance` is `NEXP`-complete** under polynomial-time many-one reductions
[Arora and Barak, draft, Chapter 2 Exercises §9 and Chapter 4 Exercises §3][AroraBarak07]. -/
theorem polyTimeComplete_NEXP :
    PolyTimeComplete @NEXP encNEXPBoundedAcceptanceInstance NEXPBoundedAcceptance :=
  ⟨mem_NEXP, polyTimeHard_NEXP⟩

/-- **If `NEXPBoundedAcceptance` is in `EXP`, then `NEXP = EXP`**
[Arora and Barak, draft, Chapter 2 Exercises §9 and Chapter 4 Exercises §3][AroraBarak07]. -/
theorem NEXP_eq_EXP_of_mem_EXP
    (h : NEXPBoundedAcceptance ∈ EXP encNEXPBoundedAcceptanceInstance)
    {α : Type} (enc : α ↪ List Bool) :
    NEXP enc = EXP enc :=
  Set.Subset.antisymm
    (fun _ hA => (polyTimeHard_NEXP enc _ hA).mem_EXP h)
    EXP_subset_NEXP

/-- **`NEXP = EXP` for every instance encoding iff `NEXPBoundedAcceptance ∈ EXP`.** -/
theorem NEXP_eq_EXP_iff :
    (∀ {α : Type} (enc : α ↪ List Bool), NEXP enc = EXP enc) ↔
      NEXPBoundedAcceptance ∈ EXP encNEXPBoundedAcceptanceInstance :=
  ⟨fun h => h encNEXPBoundedAcceptanceInstance ▸ mem_NEXP,
    fun h _ enc => NEXP_eq_EXP_of_mem_EXP h enc⟩

end NEXPBoundedAcceptance

end Cslib.Complexity
