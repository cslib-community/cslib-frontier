/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games.PolyRounds
public import CslibFrontier.Computability.Complexity.Classes.IP.Games.GoldwasserSipser

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.AffineHash
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Tactic.EncLen

/-!
# Private-coin games with polynomially many rounds and `IP[k(n)] ⊆ AM[k(n) + 2]`

Private-coin interactive games (`Cslib.Complexity.IPPolyGameClass`, `Cslib.Complexity.IPPolyRounds`)
whose move patterns, move lengths, and coin counts vary polynomially with the input length
`n = (enc a).length`, computed in polynomial time from `n` in unary. Every fixed-pattern class
`IPGameClass enc π` embeds into `IPPolyGameClass enc (fun _ => π)` and `IP[k]` embeds into
`IPPolyRounds enc (fun _ => k)`.

The main theorem is Goldwasser–Sipser [GoldwasserSipser1986] for polynomially many rounds
(`Cslib.Complexity.IPPolyRounds_subset_AMPolyRounds`): `IP[k(n)] ⊆ AM[k(n) + 2]`, without relying
on round collapse (`AMk_eq_AM`, which is unavailable when `k(n)` grows with `n`).

**Source mapping to [GoldwasserSipser1986] (paraphrase):**
* In §3, printed p. 63, a round is a pair of messages, one from each participant. The full proof
  in §4.2, printed p. 65, uses `g(n) = Q(n) / 2` such pairs. We follow that proof's total-message
  convention: its `Q(n)` is Lean's `k(n)` individual moves, and `q(n)` oracle query/reply exchanges
  give `Q(n) = k(n) = 2 * q(n)`. The last paragraph of §3 instead bounds messages sent by the
  verifier; that convention is not used to identify `Q` here. The theorem/proof is in §4.2,
  printed pp. 64–67.
* On members, some prover achieves acceptance at least `2/3`; on nonmembers, every prover's
  acceptance is at most `1/3`. Uniformity means polynomial-time shape and coin-count maps from
  unary input length
  (`encUnary` to `encIPShape` and `encUnary`, respectively), together with polynomial-time
  message and decision maps in their displayed encodings.
* The parallel repetition count `R(n) = 72 * c(n) * W(n)` and its arithmetic are original to this
  implementation. They beat the `μ ^ c(n)` soundness factor of `Emulation.three_mul_value_le_one`
  uniformly in `n` (`Cslib.Complexity.Emulation.six_mul_pow_mul_two_pow_le_three_pow`).

Proof sketch:
1. When `k(n)` is odd, the prover never sees the trailing verifier move, so folding that move into
   the verifier's final decision preserves `IPGame.bestCount`
   (`Cslib.Complexity.IPGame.bestCount_append_verifier`) and reduces the pattern to even length.
2. Emulating the even-length game appended with a final coin-revealing verifier move and merging
   adjacent Merlin moves (`Cslib.Complexity.AMGame.mergeMerlin`), plus a dummy zero-bit Arthur
   move in the odd case, gives `alternatingMoves .arthur (k(n) + 2)` directly.
3. Dynamic `agrees`, `repeatMsg`, `repeatDec`, `Emulation.check`, and `revealPayoff` run in
   polynomial time via `foldlWith_spec`.

## Main definitions

* `Cslib.Complexity.encIPMove`, `Cslib.Complexity.encIPShape`: encodings of `IPMove` and
  private-coin game shapes.
* `Cslib.Complexity.IsIPPolyGameVerifier`, `Cslib.Complexity.IPPolyGameClass`,
  `Cslib.Complexity.IPPolyRounds`: private-coin game verifiers with input-length-dependent shapes.

## Main results

* `Cslib.Complexity.IPGame.bestCount_append_verifier`,
  `Cslib.Complexity.IPk_two_mul_add_one_eq`: dropping a trailing verifier move preserves counts.
* `Cslib.Complexity.IPPolyRounds_subset_AMPolyRounds`: `IP[k(n)] ⊆ AM[k(n) + 2]`.
* `Cslib.Complexity.AMPolyGameClass_subset_IPPolyGameClass`,
  `Cslib.Complexity.AMPolyRounds_subset_IPPolyRounds`: public coins embed into private coins.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07] (locators unverified)
-/

public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM BitString.LinearHash

variable {α : Type}

/-- Boolean tag of a private-coin move: `false` for verifier, `true` for prover. -/
@[expose] def IPMove.toBool : IPMove → Bool
  | .verifier => false
  | .prover => true

/-- `IPMove.toBool` is injective. -/
theorem IPMove.toBool_injective : Function.Injective IPMove.toBool := by
  intro x y h
  cases x <;> cases y <;> simp_all [IPMove.toBool]

/-- Binary encoding of a private-coin move (`[false]` for verifier, `[true]` for prover). -/
@[expose] def encIPMove : IPMove ↪ List Bool :=
  ⟨fun m => encBool m.toBool, fun _ _ h => IPMove.toBool_injective (encBool.injective h)⟩

/-- Binary encoding of a private-coin game shape as a framed list of `(move, unary length)`
pairs. -/
abbrev encIPShape : List (IPMove × ℕ) ↪ List Bool :=
  encList (encPair encIPMove encUnary)

private theorem computableInPolyTime_ipMoveCases {γ β : Type} {encIn : γ ↪ List Bool}
    {encOut : β ↪ List Bool} {m : γ → IPMove} {f : γ → IPMove → β}
    (hm : ComputableInPolyTime m encIn encIPMove)
    (hv : ComputableInPolyTime (fun x => f x .verifier) encIn encOut)
    (hp : ComputableInPolyTime (fun x => f x .prover) encIn encOut) :
    ComputableInPolyTime (fun x => f x (m x)) encIn encOut :=
  have hb : ComputableInPolyTime (fun x => (m x).toBool) encIn encBool :=
    hm.of_enc_eq fun _ => rfl
  (hb.ite hp hv).of_enc_eq fun x => by cases m x <;> rfl

private theorem computableInPolyTime_amMoveCases {γ β : Type} {encIn : γ ↪ List Bool}
    {encOut : β ↪ List Bool} {m : γ → AMMove} {f : γ → AMMove → β}
    (hm : ComputableInPolyTime m encIn encAMMove)
    (ha : ComputableInPolyTime (fun x => f x .arthur) encIn encOut)
    (hmer : ComputableInPolyTime (fun x => f x .merlin) encIn encOut) :
    ComputableInPolyTime (fun x => f x (m x)) encIn encOut :=
  have hb : ComputableInPolyTime (fun x => (m x).toBool) encIn encBool :=
    hm.of_enc_eq fun _ => rfl
  (hb.ite hmer ha).of_enc_eq fun x => by cases m x <;> rfl

private theorem computableInPolyTime_unaryOdd {γ : Type} {encIn : γ ↪ List Bool}
    {k : γ → ℕ} (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => decide (k x % 2 = 1)) encIn encBool := by
  fun_prop

private theorem computableInPolyTime_listSum {α γ : Type} {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → List α} (hg : ComputableInPolyTime g encIn (encList encA))
    (w : α → ℕ) (hw : ComputableInPolyTime w encA encUnary)
    (hbound : ∀ x (pre : List α), pre <+: g x →
      (pre.map w).sum ≤ (encList encA (g x)).length) :
    ComputableInPolyTime (fun x => ((g x).map w).sum) encIn encUnary := by
  have hspec := ComputableInPolyTime.foldl_spec
    (encB := encUnary) (encA := encA) (encL := encList encA) (step := fun s x => s + w x)
    hg (ComputableInPolyTime.const 0) (by fun_prop)
    (fun _ pre s => s = (pre.map w).sum) (fun _ => rfl)
    (fun _ pre s val _ hs => by simp [hs])
    hg.polyBounded_length
    (fun x pre s hpre hs => by
      simpa only [hs, encUnary_apply, List.length_replicate] using hbound x pre hpre)
  exact hspec.1.of_enc_eq fun x => congrArg encUnary (hspec.2 x).symm

namespace IPGame

/-- Total transcript length is at most the encoded length of a private-coin game shape. -/
theorem transcriptLength_le_length_encIPShape (g : List (IPMove × ℕ)) :
    transcriptLength g ≤ (encIPShape g).length := by
  induction g with
  | nil => simp [transcriptLength]
  | cons x g ih =>
    obtain ⟨m, n⟩ := x
    enc_len [transcriptLength, List.map_cons, List.sum_cons, encIPShape] at ih ⊢

private theorem transcriptLength_le_of_prefix {pre g : List (IPMove × ℕ)} (h : pre <+: g) :
    transcriptLength pre ≤ transcriptLength g := by
  obtain ⟨_, rfl⟩ := h
  simp only [transcriptLength, List.map_append, List.sum_append, Nat.le_add_right]

/-- Evaluating a fixed polynomial private-coin shape `G` at unary `n` is polynomial-time. -/
theorem computableInPolyTime_evalShape (G : List (IPMove × Polynomial ℕ)) :
    ComputableInPolyTime (evalShape G) encUnary encIPShape := by
  induction G with
  | nil => exact ComputableInPolyTime.const []
  | cons x G ih =>
    obtain ⟨m, p⟩ := x
    exact (((ComputableInPolyTime.const m).prod (ComputableInPolyTime.unary_eval p)).cons'
      ih).of_enc_eq fun _ => rfl

/-- `toAM` on a polynomial-time shape is polynomial-time. -/
theorem computableInPolyTime_toAM_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → List (IPMove × ℕ)} (hg : ComputableInPolyTime g encIn encIPShape) :
    ComputableInPolyTime (fun x => toAM (g x)) encIn encAMShape := by
  have h1 : ComputableInPolyTime (fun x : γ × (IPMove × ℕ) => x.2.1.toAM)
      (encPair encIn (encPair encIPMove encUnary)) encAMMove :=
    (show ComputableInPolyTime (fun x : γ × (IPMove × ℕ) => x.2.1)
        (encPair encIn (encPair encIPMove encUnary)) encIPMove by fun_prop).of_enc_eq
      fun x => by cases x.2.1 <;> rfl
  exact (ComputableInPolyTime.mapWithInput hg (f := fun _ x => (x.1.toAM, x.2))
    (h1.prod (by fun_prop))).of_enc_eq fun _ => rfl

/-- `transcriptLength` on a polynomial-time private-coin shape is polynomial-time. -/
theorem computableInPolyTime_transcriptLength_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → List (IPMove × ℕ)} (hg : ComputableInPolyTime g encIn encIPShape) :
    ComputableInPolyTime (fun x => transcriptLength (g x)) encIn encUnary :=
  computableInPolyTime_listSum hg Prod.snd (by fun_prop) fun x pre hpre =>
    (transcriptLength_le_of_prefix hpre).trans (transcriptLength_le_length_encIPShape (g x))

/-- `verifierMoves` on a polynomial-time private-coin shape is polynomial-time. -/
theorem computableInPolyTime_verifierMoves_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → List (IPMove × ℕ)} (hg : ComputableInPolyTime g encIn encIPShape) :
    ComputableInPolyTime (fun x => verifierMoves (g x)) encIn encUnary := by
  have hw : ComputableInPolyTime (fun e : IPMove × ℕ => if e.1 = .verifier then 1 else 0)
      (encPair encIPMove encUnary) encUnary :=
    computableInPolyTime_ipMoveCases (f := fun _ m => if m = .verifier then 1 else 0)
      (by fun_prop) (by fun_prop) (by fun_prop)
  refine (computableInPolyTime_listSum hg _ hw fun x pre hpre => ?_).of_enc_eq fun x =>
    congrArg encUnary ?_
  · have hle : (pre.map fun e => if e.1 = .verifier then 1 else 0).sum ≤ pre.length := by
      clear hpre
      induction pre with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        split_ifs <;> omega
    exact hle.trans (hpre.length_le.trans
      (SizedListEncoding.length_le (encA := encPair encIPMove encUnary) (encL := encIPShape) _))
  · induction g x with
    | nil => rfl
    | cons a l ih =>
      rw [verifierMoves] at ih ⊢
      rcases a with ⟨_ | _, _⟩
      · simp only [List.map_cons, List.sum_cons, List.count_cons, beq_self_eq_true, ↓reduceIte, ih]
        exact Nat.add_comm _ 1
      · simp only [List.map_cons, List.sum_cons, List.count_cons, reduceCtorEq, beq_iff_eq,
          ↓reduceIte, add_zero, zero_add, ih]

/-- `moveLength` on a polynomial-time private-coin shape is polynomial-time. -/
theorem computableInPolyTime_moveLength_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → List (IPMove × ℕ)} {j : γ → ℕ}
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => moveLength (g x) (j x)) encIn encUnary := by
  refine ((ComputableInPolyTime.snd encIPMove encUnary).comp
    (ComputableInPolyTime.listGetDWithInput hg hj (.prover, 0))).of_enc_eq fun x =>
      congrArg encUnary ?_
  simp only [Function.comp_apply, moveLength, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (g x)[j x]? <;> simp

/-! ### Dropping a trailing verifier move -/

/-- `agrees` splits cleanly across concatenated shapes when the prefix transcript matches the
prefix shape length. -/
theorem agrees_append (msg : ℕ → List Bool → List Bool) (g h : List (IPMove × ℕ))
    (j : ℕ) (p t u : List Bool) (ht : t.length = transcriptLength g) :
    agrees msg (g ++ h) j p (t ++ u) =
      (agrees msg g j p t && agrees msg h (j + g.length) (p ++ t) u) := by
  induction g generalizing j p t with
  | nil =>
    obtain rfl : t = [] := List.eq_nil_of_length_eq_zero (by simpa [transcriptLength] using ht)
    simp [agrees]
  | cons x g ih =>
    obtain ⟨v, n⟩ := x
    simp only [transcriptLength, List.map_cons, List.sum_cons] at ht
    have htake : (t ++ u).take n = t.take n := List.take_append_of_le_length (by omega)
    have hdrop : (t ++ u).drop n = t.drop n ++ u := List.drop_append_of_le_length (by omega)
    have hsub : (t.drop n).length = transcriptLength g := by
      simp [List.length_drop, transcriptLength, ht]
    have htd : t.take n ++ t.drop n = t := List.take_append_drop n t
    have ih' := ih (j + 1) (p ++ t.take n) (t.drop n) hsub
    rw [show j + 1 + g.length = j + (g.length + 1) by omega,
      List.append_assoc, htd] at ih'
    cases v <;> simp only [List.cons_append, agrees, htake, hdrop, ih', List.length_cons,
      Bool.and_assoc]

/-- Dropping a trailing verifier move by folding its message directly into the verifier's final
decision preserves `bestCount`. -/
theorem bestCount_append_verifier {ρ : ℕ} (msg : BitString ρ → ℕ → List Bool → List Bool)
    (dec : BitString ρ → List Bool → Bool) (g : List (IPMove × ℕ)) (L : ℕ) :
    bestCount msg dec (g ++ [(.verifier, L)]) =
      bestCount msg
        (fun c t => dec c (t ++ List.ofFn (BitString.ofList L (msg c g.length t)))) g := by
  unfold bestCount
  rw [count_append]
  refine count_congr_of_length g fun t ht => ?_
  rw [count_verifier]
  simp only [count_nil, acceptedCoins]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun c : BitString ρ =>
      BitString.ofList L (msg c g.length t)) (t := univ) fun _ _ => mem_univ _]
  refine sum_congr rfl fun m _ => ?_
  rw [Finset.filter_filter]
  congr 1
  ext c
  have hag := agrees_append (msg c) g [(.verifier, L)] 0 [] t (List.ofFn m) ht
  have hm_len : (List.ofFn m).length ≤ L := by simp
  simp only [List.nil_append, zero_add, agrees, List.take_of_length_le hm_len,
    Bool.and_true, List.ofFn_inj, eq_comm (a := m)] at hag
  simp only [List.append_nil, mem_filter, mem_univ, true_and, Bool.and_eq_true,
    decide_eq_true_eq, hag]
  exact ⟨fun ⟨⟨hg, hm⟩, hd⟩ => ⟨⟨hg, hm ▸ hd⟩, hm⟩,
    fun ⟨⟨hg, hd⟩, hm⟩ => ⟨⟨hg, hm⟩, hm.symm ▸ hd⟩⟩

/-! ### Dynamic polynomial-time `agrees`, `repeatMsg`, and `repeatDec` -/

/-- State for folding `agrees` across the transcript. -/
private structure AgreesState where
  /-- Current message index. -/
  j : ℕ
  /-- Accumulated transcript prefix. -/
  p : List Bool
  /-- Remaining transcript suffix. -/
  t : List Bool
  /-- Whether all messages agree so far. -/
  ok : Bool
  deriving Repr, DecidableEq

/-- Encoding for `AgreesState`. -/
private enc_structure encAgreesState : AgreesState where
  j : encUnary, p : encBits, t : encBits, ok : encBool

private def agreesStep (msg : α × List Bool × ℕ × List Bool → List Bool)
    (par : α × List Bool) (st : AgreesState) (x : IPMove × ℕ) : AgreesState :=
  let {j, p, t, ok} := st
  let ok' := ok && match x.1 with
    | .verifier => decide (t.take x.2 = BitString.listRow x.2 0 (msg (par.1, par.2, j, p)))
    | .prover => true
  { j := j + 1, p := p ++ t.take x.2, t := t.drop x.2, ok := ok' }

private theorem foldl_agreesStep (msg : α × List Bool × ℕ × List Bool → List Bool)
    (a : α) (c : List Bool) (g : List (IPMove × ℕ)) (j : ℕ) (p t : List Bool) (ok : Bool) :
    (g.foldl (agreesStep msg (a, c)) { j := j, p := p, t := t, ok := ok }).ok =
      (ok && agrees (fun j' p' => msg (a, c, j', p')) g j p t) := by
  fun_induction agrees (fun j' p' => msg (a, c, j', p')) g j p t generalizing ok <;>
    simp only [List.foldl_nil, List.foldl_cons, agreesStep, BitString.listRow_zero, Bool.and_assoc,
      Bool.and_true, *]

/-- `agrees` on a dynamic polynomial-time shape `g` is polynomial-time. -/
theorem computableInPolyTime_agrees_dyn {γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {a : γ → α} {c : γ → List Bool} {g : γ → List (IPMove × ℕ)} {j₀ : γ → ℕ}
    {p₀ t₀ : γ → List Bool}
    {msg : α × List Bool × ℕ × List Bool → List Bool}
    (ha : ComputableInPolyTime a encIn enc)
    (hc : ComputableInPolyTime c encIn encBits)
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hj₀ : ComputableInPolyTime j₀ encIn encUnary)
    (hp₀ : ComputableInPolyTime p₀ encIn encBits)
    (ht₀ : ComputableInPolyTime t₀ encIn encBits)
    (hmsg : ComputableInPolyTime msg (encMsgInput enc) encBits) :
    ComputableInPolyTime
      (fun x => agrees (fun j p => msg (a x, c x, j, p)) (g x) (j₀ x) (p₀ x) (t₀ x))
      encIn encBool := by
  let encAg : (((α × List Bool) × AgreesState) × (IPMove × ℕ)) ↪ List Bool :=
    encPair (encPair (encPair enc encBits) encAgreesState) (encPair encIPMove encUnary)
  have hstep : ComputableInPolyTime
      (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) => agreesStep msg q.1.1 q.1.2 q.2)
      encAg encAgreesState := by
    have hst : ComputableInPolyTime (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) =>
        q.1.2) encAg encAgreesState := (ComputableInPolyTime.fst _ _).snd'
    have hj' := encAgreesState_j_polyTime hst
    have hp' := encAgreesState_p_polyTime hst
    have ht' := encAgreesState_t_polyTime hst
    have hn' : ComputableInPolyTime (fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) =>
        q.2.2) encAg encUnary := (ComputableInPolyTime.snd _ _).snd'
    have htake := ht'.bitsTakeWithInput hn'
    have hmsg' := hmsg.comp ((ComputableInPolyTime.fst _ _).fst'.fst'.prod
      ((ComputableInPolyTime.fst _ _).fst'.snd'.prod (hj'.prod hp')))
    have hcheck := computableInPolyTime_ipMoveCases
      (m := fun q : ((α × List Bool) × AgreesState) × (IPMove × ℕ) => q.2.1)
      (f := fun q m => match m with
        | .verifier => decide (q.1.2.t.take q.2.2 =
            BitString.listRow q.2.2 0 (msg (q.1.1.1, q.1.1.2, q.1.2.j, q.1.2.p)))
        | .prover => true)
      (ComputableInPolyTime.snd _ _).fst'
      (htake.decide_eq' (hn'.bitsRowWithInput (.const 0) hmsg')) (.const true)
    exact (encAgreesState_mk_polyTime (hj'.unary_add' (.const 1)) (hp'.bitsAppend htake)
      (ht'.bitsDropWithInput hn') ((encAgreesState_ok_polyTime hst).bool_and' hcheck)).of_enc_eq
      fun _ => rfl
  have hbound : PolyBounded (fun x => (encIn x).length)
      (fun x => 2 * ((encUnary (j₀ x)).length + (encIPShape (g x)).length) +
        4 * ((encBits (p₀ x)).length + (encBits (t₀ x)).length) + 6) :=
    (((PolyBounded.const 2).mul (hj₀.polyBounded_length.add hg.polyBounded_length)).add
      ((PolyBounded.const 4).mul (hp₀.polyBounded_length.add ht₀.polyBounded_length))).add
        (.const 6)
  have hspec := ComputableInPolyTime.foldlWith_spec
    (encP := encPair enc encBits) (encB := encAgreesState)
    (encA := encPair encIPMove encUnary) (encL := encIPShape)
    (par := fun x => (a x, c x)) (list := g)
    (init := fun x => { j := j₀ x, p := p₀ x, t := t₀ x, ok := true }) (step := agreesStep msg)
    (ha.prod hc) hg (by fun_prop) hstep
    (fun x pre st => st.j = j₀ x + pre.length ∧
      st.p.length + st.t.length ≤ (p₀ x).length + (t₀ x).length)
    (fun _ => ⟨rfl, le_rfl⟩)
    (fun _ _ ⟨j, p, t, ok⟩ _ _ ⟨hj', hlen'⟩ => by
      simp only [agreesStep, List.length_append, List.length_singleton, List.length_take,
        List.length_drop] at hj' hlen' ⊢
      exact ⟨by omega, by omega⟩)
    hbound
    (fun x pre st hpre ⟨hj', hlen'⟩ => by
      have hpfx : pre.length ≤ (encIPShape (g x)).length :=
        hpre.length_le.trans
          (SizedListEncoding.length_le (encA := encPair encIPMove encUnary) (encL := encIPShape) _)
      simp only [encAgreesState_apply, length_encPair, encUnary_apply,
        List.length_replicate, encBits_apply, encBool_apply, List.length_singleton]
      omega)
  exact ((show ComputableInPolyTime (fun st : AgreesState => st.ok) encAgreesState encBool by
    fun_prop).comp hspec.1).of_enc_eq fun x => by
    simp only [Function.comp_apply, foldl_agreesStep, Bool.true_and]

/-- `repeatShape` for a dynamic shape and repetition count is polynomial-time. -/
theorem computableInPolyTime_repeatShape_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {t : γ → ℕ} {g : γ → List (IPMove × ℕ)}
    (ht : ComputableInPolyTime t encIn encUnary)
    (hg : ComputableInPolyTime g encIn encIPShape) :
    ComputableInPolyTime (fun x => repeatShape (t x) (g x)) encIn encIPShape :=
  (ComputableInPolyTime.mapWithInput hg (f := fun x (e : IPMove × ℕ) => (e.1, t x * e.2))
    (by fun_prop)).of_enc_eq fun _ => rfl

/-- `repeatMsg` on dynamic `T`, `ρ`, and shape `g` is polynomial-time. -/
theorem computableInPolyTime_repeatMsg_dyn {γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {a : γ → α} {c : γ → List Bool} {g : γ → List (IPMove × ℕ)} {T ρ j : γ → ℕ}
    {p : γ → List Bool} {msg : α × List Bool × ℕ × List Bool → List Bool}
    (ha : ComputableInPolyTime a encIn enc)
    (hc : ComputableInPolyTime c encIn encBits)
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hT : ComputableInPolyTime T encIn encUnary)
    (hρ : ComputableInPolyTime ρ encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary)
    (hp : ComputableInPolyTime p encIn encBits)
    (hmsg : ComputableInPolyTime msg (encMsgInput enc) encBits) :
    ComputableInPolyTime
      (fun x => repeatMsg (T x) (g x)
        (fun i => fun j' p' => msg (a x, BitString.listRow (ρ x) i (c x), j', p'))
        (j x) (p x))
      encIn encBits := by
  have hx1 : ComputableInPolyTime (fun y : γ × ℕ => y.1) (encPair encIn encUnary) encIn := .fst _ _
  have htake := computableInPolyTime_toAM_dyn
    (ComputableInPolyTime.listTakeWithInput (hg.comp hx1) (hj.comp hx1))
  have hcopy := AMGame.computableInPolyTime_copyTranscript_dyn
    (hT.comp hx1) (.snd _ _) htake (hp.comp hx1)
  have hlen := computableInPolyTime_moveLength_dyn (hg.comp hx1) (hj.comp hx1)
  have hrow := ComputableInPolyTime.bitsRowWithInput (hρ.comp hx1) (.snd _ _) (hc.comp hx1)
  have hm := hmsg.comp ((ha.comp hx1).prod (hrow.prod ((hj.comp hx1).prod hcopy)))
  exact (ComputableInPolyTime.flatMapToBitsWithInput
    (f := fun x i => BitString.listRow (moveLength (g x) (j x)) 0
      (msg (a x, BitString.listRow (ρ x) i (c x), j x,
        AMGame.copyTranscript (T x) i (toAM ((g x).take (j x))) (p x))))
    (ComputableInPolyTime.range.comp hT) (by fun_prop)).of_enc_eq fun x => congrArg _ (by
      simp only [repeatMsg, BitString.listRow_zero]; rfl)

/-- `repeatDec` on dynamic `T`, `ρ`, and shape `g` is polynomial-time. -/
theorem computableInPolyTime_repeatDec_dyn {γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {a : γ → α} {c : γ → List Bool} {g : γ → List (IPMove × ℕ)} {T ρ : γ → ℕ}
    {w : γ → List Bool} {dec : α × List Bool × List Bool → Bool}
    (ha : ComputableInPolyTime a encIn enc)
    (hc : ComputableInPolyTime c encIn encBits)
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hT : ComputableInPolyTime T encIn encUnary)
    (hρ : ComputableInPolyTime ρ encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits)
    (hdec : ComputableInPolyTime dec (encDecInput enc) encBool) :
    ComputableInPolyTime
      (fun x => repeatDec (T x) (g x)
        (fun i t => dec (a x, BitString.listRow (ρ x) i (c x), t)) (w x))
      encIn encBool := by
  have hx1 : ComputableInPolyTime (fun y : γ × ℕ => y.1) (encPair encIn encUnary) encIn := .fst _ _
  have hcopy := AMGame.computableInPolyTime_copyTranscript_dyn
    (hT.comp hx1) (.snd _ _) (computableInPolyTime_toAM_dyn (hg.comp hx1)) (hw.comp hx1)
  have hrow := ComputableInPolyTime.bitsRowWithInput (hρ.comp hx1) (.snd _ _) (hc.comp hx1)
  exact ComputableInPolyTime.allWithInput
    (test := fun x i => dec (a x, BitString.listRow (ρ x) i (c x),
      AMGame.copyTranscript (T x) i (toAM (g x)) (w x)))
    (ComputableInPolyTime.range.comp hT) (hdec.comp ((ha.comp hx1).prod (hrow.prod hcopy)))

end IPGame

namespace Emulation

open IPGame

/-- `Emulation.shape B Z` for dynamic `B`, `Z`, and `g` is polynomial-time. -/
theorem computableInPolyTime_shape_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {B Z : γ → ℕ} {g : γ → List (IPMove × ℕ)}
    (hB : ComputableInPolyTime B encIn encUnary)
    (hZ : ComputableInPolyTime Z encIn encUnary)
    (hg : ComputableInPolyTime g encIn encIPShape) :
    ComputableInPolyTime (fun x => shape (B x) (Z x) (g x)) encIn encAMShape := by
  let stepFn : γ → IPMove × ℕ → List (AMMove × ℕ) := fun x y => match y.1 with
    | .verifier => [(.arthur, B x * (y.2 + Z x) + B x), (.merlin, B x + (y.2 + Z x))]
    | .prover => [(.merlin, y.2)]
  have hf : ComputableInPolyTime (fun p : γ × (IPMove × ℕ) => stepFn p.1 p.2)
      (encPair encIn (encPair encIPMove encUnary)) encAMShape :=
    computableInPolyTime_ipMoveCases (encOut := encAMShape)
      (f := fun (p : γ × (IPMove × ℕ)) (m : IPMove) => stepFn p.1 (m, p.2.2))
      (by fun_prop) (by dsimp only [stepFn]; fun_prop) (by dsimp only [stepFn]; fun_prop)
  refine (ComputableInPolyTime.flatMapWithInput (f := stepFn) hg hf).of_enc_eq
    fun x => congrArg encAMShape ?_
  induction g x with
  | nil => rfl
  | cons y ys ih => obtain ⟨_ | _, n⟩ := y <;> simp [shape, stepFn, ih]

/-- State for folding `check` across the transcript. -/
private structure CheckState where
  /-- Current logarithmic size claim. -/
  κ : ℕ
  /-- Decoded private-game transcript prefix. -/
  p : List Bool
  /-- Remaining emulation transcript. -/
  w : List Bool
  /-- Whether all checks pass so far. -/
  ok : Bool
  deriving Repr, DecidableEq

/-- Encoding for `CheckState`. -/
private enc_structure encCheckState : CheckState where
  κ : encUnary, p : encBits, w : encBits, ok : encBool

private def checkStep (B Z K : ℕ) (st : CheckState) (move : IPMove × ℕ) : CheckState :=
  let {κ, p, w, ok} := st
  match move with
  | (.verifier, n) =>
    let r := w.take (B * (n + Z) + B)
    let y := w.drop (B * (n + Z) + B)
    let b := (y.take B).count true
    let x := (y.drop B).take (n + Z)
    let ok' := ok && hashZero B (n + Z) r x &&
      (!((x.drop n).take (Z + κ - (b + K))).any fun b => b)
    { κ := b, p := p ++ x.take n, w := (y.drop B).drop (n + Z), ok := ok' }
  | (.prover, n) =>
    { κ := κ, p := p ++ w.take n, w := w.drop n, ok := ok }

private theorem foldl_checkStep (B Z K : ℕ) (V : List Bool → Bool)
    (g : List (IPMove × ℕ)) (κ : ℕ) (p w : List Bool) (ok : Bool) :
    (let st := g.foldl (checkStep B Z K) { κ := κ, p := p, w := w, ok := ok };
      st.ok && decide (st.κ = 0) && V st.p) =
      (ok && check B Z K V g κ p w) := by
  induction g generalizing κ p w ok with
  | nil => exact Bool.and_assoc _ _ _
  | cons a g ih =>
    rcases a with ⟨_ | _, n⟩ <;> dsimp only
    · rw [List.foldl_cons, checkStep, ih, check]
      simp only [Bool.and_assoc]
    · rw [List.foldl_cons, checkStep, ih, check]

private theorem computableInPolyTime_checkStep :
    ComputableInPolyTime
      (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) =>
        checkStep q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2 q.2)
      (encPair (encPair (encPair encUnary (encPair encUnary encUnary)) encCheckState)
        (encPair encIPMove encUnary))
      encCheckState := by
  let encCh := encPair (encPair (encPair encUnary (encPair encUnary encUnary)) encCheckState)
    (encPair encIPMove encUnary)
  have hstq : ComputableInPolyTime
      (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.1.2) encCh encCheckState :=
    (ComputableInPolyTime.fst _ _).snd'
  have hnq : ComputableInPolyTime
      (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.2.2) encCh encUnary :=
    (ComputableInPolyTime.snd _ _).snd'
  have hwq := encCheckState_w_polyTime hstq
  have hpq := encCheckState_p_polyTime hstq
  have hκq := encCheckState_κ_polyTime hstq
  have hokq := encCheckState_ok_polyTime hstq
  have hvBranch : ComputableInPolyTime
      (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) =>
        checkStep q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2 (.verifier, q.2.2))
      encCh encCheckState := by
    have hBq : ComputableInPolyTime (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) =>
        q.1.1.1) encCh encUnary := (ComputableInPolyTime.fst _ _).fst'.fst'
    have hZq : ComputableInPolyTime (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) =>
        q.1.1.2.1) encCh encUnary := (ComputableInPolyTime.fst _ _).fst'.snd'.fst'
    have hKq : ComputableInPolyTime (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) =>
        q.1.1.2.2) encCh encUnary := (ComputableInPolyTime.fst _ _).fst'.snd'.snd'
    have hnZ := hnq.unary_add' hZq
    have hP := (hBq.unary_mul' hnZ).unary_add' hBq
    have hy := hwq.bitsDropWithInput hP
    have hb := (hy.bitsTakeWithInput hBq).bitsCountWithInput (ComputableInPolyTime.const true)
    have hyB := hy.bitsDropWithInput hBq
    have hx := hyB.bitsTakeWithInput hnZ
    have hhash := computableInPolyTime_hashZero hBq hnZ (hwq.bitsTakeWithInput hP) hx
    have hpad := ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.bitsAnyWithInput
      (test := fun _ b => b)
      ((hx.bitsDropWithInput hnq).bitsTakeWithInput ((hZq.unary_add' hκq).unary_sub'
        (hb.unary_add' hKq))) (ComputableInPolyTime.snd _ _))
    exact (encCheckState_mk_polyTime hb (hpq.bitsAppend (hx.bitsTakeWithInput hnq))
      (hyB.bitsDropWithInput hnZ) ((hokq.bool_and' hhash).bool_and' hpad)).of_enc_eq fun _ => rfl
  have hpBranch : ComputableInPolyTime
      (fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) =>
        checkStep q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2 (.prover, q.2.2))
      encCh encCheckState :=
    (encCheckState_mk_polyTime hκq (hpq.bitsAppend (hwq.bitsTakeWithInput hnq))
      (hwq.bitsDropWithInput hnq) hokq).of_enc_eq fun _ => rfl
  exact computableInPolyTime_ipMoveCases
    (m := fun q : ((ℕ × ℕ × ℕ) × CheckState) × (IPMove × ℕ) => q.2.1)
    (f := fun q m => checkStep q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2 (m, q.2.2))
    (by fun_prop) hvBranch hpBranch

/-- **`Emulation.check` on a dynamic shape `g` is polynomial-time.** -/
theorem computableInPolyTime_check_dyn {γ : Type} {encIn : γ ↪ List Bool}
    {B Z K : γ → ℕ} {g : γ → List (IPMove × ℕ)} {V : γ → List Bool → Bool}
    {κ : γ → ℕ} {p w : γ → List Bool}
    (hB : ComputableInPolyTime B encIn encUnary)
    (hZ : ComputableInPolyTime Z encIn encUnary)
    (hK : ComputableInPolyTime K encIn encUnary)
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hV : ∀ {q : γ → List Bool}, ComputableInPolyTime q encIn encBits →
      ComputableInPolyTime (fun x => V x (q x)) encIn encBool)
    (hκ : ComputableInPolyTime κ encIn encUnary)
    (hp : ComputableInPolyTime p encIn encBits)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime
      (fun x => check (B x) (Z x) (K x) (V x) (g x) (κ x) (p x) (w x)) encIn encBool := by
  have hbound : PolyBounded (fun x => (encIn x).length)
      (fun x => 2 * ((encUnary (B x)).length + (encUnary (κ x)).length) +
        4 * ((encBits (p x)).length + (encIPShape (g x)).length + (encBits (w x)).length) + 8) :=
    (((PolyBounded.const 2).mul (hB.polyBounded_length.add hκ.polyBounded_length)).add
      ((PolyBounded.const 4).mul
        ((hp.polyBounded_length.add hg.polyBounded_length).add hw.polyBounded_length))).add
        (.const 8)
  have hspec := ComputableInPolyTime.foldlWith_spec
    (encP := encPair encUnary (encPair encUnary encUnary))
    (encB := encCheckState) (encA := encPair encIPMove encUnary) (encL := encIPShape)
    (par := fun x => (B x, Z x, K x)) (list := g)
    (init := fun x => { κ := κ x, p := p x, w := w x, ok := true })
    (step := fun par => checkStep par.1 par.2.1 par.2.2)
    (by fun_prop) hg (by fun_prop) computableInPolyTime_checkStep
    (fun x pre st => st.κ ≤ max (κ x) (B x) ∧
      st.p.length ≤ (p x).length + transcriptLength pre ∧ st.w.length ≤ (w x).length)
    (fun _ => ⟨le_max_left _ _, by simp, le_rfl⟩)
    (fun x pre ⟨κ', p', w', ok'⟩ ⟨m, n⟩ _ ⟨hκ', hp', hw'⟩ => by
      cases m <;>
        refine ⟨?_, ?_, by simp only [checkStep, List.length_drop] at hw' ⊢; omega⟩ <;>
        first
        | exact (List.count_le_length.trans (by simp)).trans (le_max_right _ _)
        | exact hκ'
        | (simp only [checkStep, List.length_append, List.length_take, transcriptLength,
            List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
            List.sum_nil, add_zero] at hp' ⊢; omega))
    hbound
    (fun x pre st hpre ⟨hκ', hp', hw'⟩ => by
      have htr : transcriptLength pre ≤ (encIPShape (g x)).length :=
        (transcriptLength_le_of_prefix hpre).trans (transcriptLength_le_length_encIPShape (g x))
      simp only [encCheckState_apply, length_encPair, encUnary_apply, List.length_replicate,
        encBits_apply, encBool_apply, List.length_singleton]
      omega)
  have hst := hspec.1
  exact (((encCheckState_ok_polyTime hst).bool_and'
    ((encCheckState_κ_polyTime hst).decide_eq' (.const 0))).bool_and'
    (hV (encCheckState_p_polyTime hst))).of_enc_eq fun x => by
    simpa only [Bool.true_and] using
      congrArg encBool (foldl_checkStep (B x) (Z x) (K x) (V x) (g x) (κ x) (p x) (w x) true).symm

/-- `revealPayoff` on a dynamic shape `g` is polynomial-time. -/
theorem computableInPolyTime_revealPayoff_dyn {γ : Type} {enc : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {a : γ → α} {g : γ → List (IPMove × ℕ)} {L : γ → ℕ}
    {msg : α × List Bool × ℕ × List Bool → List Bool} {dec : α × List Bool × List Bool → Bool}
    {w : γ → List Bool}
    (ha : ComputableInPolyTime a encIn enc)
    (hg : ComputableInPolyTime g encIn encIPShape)
    (hL : ComputableInPolyTime L encIn encUnary)
    (hmsg : ComputableInPolyTime msg (encMsgInput enc) encBits)
    (hdec : ComputableInPolyTime dec (encDecInput enc) encBool)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime
      (fun x => revealPayoff (fun c j p => msg (a x, c, j, p)) (fun c t => dec (a x, c, t))
        (g x) (L x) (w x))
      encIn encBool := by
  have hc := ComputableInPolyTime.bitsDropWithInput hw hL
  have ht := ComputableInPolyTime.bitsTakeWithInput hw hL
  have hag := IPGame.computableInPolyTime_agrees_dyn ha hc hg
    (ComputableInPolyTime.const 0) (ComputableInPolyTime.const []) ht hmsg
  have hd := hdec.comp (ha.prod (hc.prod ht))
  exact (ComputableInPolyTime.bool_and' hag hd).of_enc_eq fun _ => rfl

/-- State for folding adjacent Merlin moves in AM games. -/
private structure MergeState where
  /-- Pending accumulated Merlin length. -/
  pending : Option ℕ
  /-- Reversed compacted shape so far. -/
  history : List (AMMove × ℕ)
  deriving Repr, DecidableEq

/-- Encoding for `MergeState`. -/
private enc_structure encMergeState : MergeState where
  pending : (encOption encUnary), history : encAMShape

private def mergeStep (st : MergeState) (x : AMMove × ℕ) : MergeState :=
  match x.1 with
  | .merlin => MergeState.mk (some (st.pending.getD 0 + x.2)) st.history
  | .arthur =>
    match st.pending with
    | none => (MergeState.mk none ((.arthur, x.2) :: st.history))
    | some m => (MergeState.mk none ((.arthur, x.2) :: (.merlin, m) :: st.history))

private def mergeFlush (st : MergeState) : List (AMMove × ℕ) :=
  (match st.pending with
    | none => st.history
    | some m => (.merlin, m) :: st.history).reverse

private theorem mergeMerlin_append_arthur_cons (pref : List (AMMove × ℕ)) (n : ℕ)
    (g : List (AMMove × ℕ)) :
    AMGame.mergeMerlin (pref ++ (.arthur, n) :: g) =
      AMGame.mergeMerlin pref ++ (.arthur, n) :: AMGame.mergeMerlin g := by
  induction pref with
  | nil => rfl
  | cons x pref ih =>
    obtain ⟨_ | _, m⟩ := x
    · simp [AMGame.mergeMerlin, ih]
    · simp only [List.cons_append, AMGame.mergeMerlin, ih]
      cases h : AMGame.mergeMerlin pref with
      | nil => rfl
      | cons y tail =>
        obtain ⟨_ | _, m'⟩ := y <;> rfl

private theorem mergeMerlin_append_of_head_ne (acc : List (AMMove × ℕ))
    (hhead : acc.head?.map Prod.fst ≠ some .merlin) (u : List (AMMove × ℕ)) :
    AMGame.mergeMerlin (acc.reverse ++ u) =
      AMGame.mergeMerlin acc.reverse ++ AMGame.mergeMerlin u := by
  cases acc with
  | nil => rfl
  | cons y tail =>
    obtain ⟨_ | _, k⟩ := y
    · rw [List.reverse_cons, List.append_assoc, List.singleton_append,
        mergeMerlin_append_arthur_cons tail.reverse k u,
        mergeMerlin_append_arthur_cons tail.reverse k []]
      simp only [AMGame.mergeMerlin, List.append_assoc, List.singleton_append]
    · simp at hhead

private theorem mergeMerlin_merlin_merlin (m n : ℕ) (g : List (AMMove × ℕ)) :
    AMGame.mergeMerlin ((.merlin, m) :: (.merlin, n) :: g) =
      AMGame.mergeMerlin ((.merlin, m + n) :: g) := by
  simp only [AMGame.mergeMerlin]
  cases h : AMGame.mergeMerlin g with
  | nil => rfl
  | cons y tail =>
    obtain ⟨_ | _, k⟩ := y
    · rfl
    · simp [Nat.add_assoc]

private theorem mergeMerlin_eq_mergeFlush_aux (g acc : List (AMMove × ℕ))
    (hacc : AMGame.mergeMerlin acc.reverse = acc.reverse)
    (hhead : acc.head?.map Prod.fst ≠ some .merlin) :
    ∀ p : Option ℕ,
      AMGame.mergeMerlin (acc.reverse ++
        match p with | none => g | some m => (.merlin, m) :: g) =
      mergeFlush (g.foldl mergeStep (MergeState.mk p acc)) := by
  induction g generalizing acc with
  | nil =>
    intro p
    rcases p with _ | m
    · simp only [List.append_nil, List.foldl_nil, mergeFlush]
      exact hacc
    · simp only [List.foldl_nil, mergeFlush, List.reverse_cons]
      rw [mergeMerlin_append_of_head_ne acc hhead [(.merlin, m)], hacc]
      rfl
  | cons x g ih =>
    intro p
    obtain ⟨_ | _, n⟩ := x
    · rcases p with _ | m
      · simp only [List.foldl_cons, mergeStep]
        have hacc' : AMGame.mergeMerlin ((.arthur, n) :: acc).reverse =
            ((.arthur, n) :: acc).reverse := by
          rw [List.reverse_cons, mergeMerlin_append_of_head_ne acc hhead [(.arthur, n)], hacc]
          rfl
        simpa [List.reverse_cons, List.append_assoc] using
          ih ((.arthur, n) :: acc) hacc' (by simp) none
      · simp only [List.foldl_cons, mergeStep]
        have haccM : AMGame.mergeMerlin (acc.reverse ++ [(.merlin, m)]) =
            acc.reverse ++ [(.merlin, m)] := by
          rw [mergeMerlin_append_of_head_ne acc hhead [(.merlin, m)], hacc]; rfl
        have hleft : AMGame.mergeMerlin (acc.reverse ++ (.merlin, m) :: (.arthur, n) :: g) =
            AMGame.mergeMerlin (((.arthur, n) :: (.merlin, m) :: acc).reverse ++ g) := by
          rw [show ((.arthur, n) :: (.merlin, m) :: acc).reverse ++ g =
              (acc.reverse ++ [(.merlin, m)]) ++ (.arthur, n) :: g by
            simp [List.reverse_cons, List.append_assoc],
            mergeMerlin_append_arthur_cons _ n g, haccM,
            mergeMerlin_append_of_head_ne acc hhead, hacc]
          simp [AMGame.mergeMerlin]
        have hacc2 : AMGame.mergeMerlin ((.arthur, n) :: (.merlin, m) :: acc).reverse =
            ((.arthur, n) :: (.merlin, m) :: acc).reverse := by
          rw [List.reverse_cons, mergeMerlin_append_arthur_cons _ n [], List.reverse_cons, haccM]
          rfl
        exact hleft.trans (ih ((.arthur, n) :: (.merlin, m) :: acc) hacc2 (by simp) none)
    · rcases p with _ | m
      · simpa [List.foldl_cons, mergeStep, Nat.zero_add] using
          ih acc hacc hhead (some n)
      · have ih' := ih acc hacc hhead (some (m + n))
        have hmer : AMGame.mergeMerlin (acc.reverse ++ (.merlin, m) :: (.merlin, n) :: g) =
            AMGame.mergeMerlin (acc.reverse ++ (.merlin, m + n) :: g) := by
          rw [mergeMerlin_append_of_head_ne acc hhead ((.merlin, m) :: (.merlin, n) :: g),
            mergeMerlin_append_of_head_ne acc hhead ((.merlin, m + n) :: g),
            mergeMerlin_merlin_merlin]
        exact hmer.trans (by simpa [List.foldl_cons, mergeStep] using ih')

private theorem mergeMerlin_eq_mergeFlush (g : List (AMMove × ℕ)) :
    AMGame.mergeMerlin g = mergeFlush (g.foldl mergeStep (MergeState.mk none [])) :=
  mergeMerlin_eq_mergeFlush_aux g [] rfl (by simp) none

private theorem computableInPolyTime_mergeStep :
    ComputableInPolyTime (fun q : MergeState × (AMMove × ℕ) => mergeStep q.1 q.2)
      (encPair encMergeState (encPair encAMMove encUnary)) encMergeState := by
  let encMe := encPair encMergeState (encPair encAMMove encUnary)
  have haBranch : ComputableInPolyTime
      (fun q : MergeState × (AMMove × ℕ) => mergeStep q.1 (.arthur, q.2.2))
      encMe encMergeState := by
    have hnone : ComputableInPolyTime
        (fun q : MergeState × (AMMove × ℕ) =>
          MergeState.mk none ((AMMove.arthur, q.2.2) :: q.1.history)) encMe encMergeState := by
      fun_prop
    have hsome : ComputableInPolyTime
        (fun p : (MergeState × (AMMove × ℕ)) × ℕ =>
          MergeState.mk none ((AMMove.arthur, p.1.2.2) :: (AMMove.merlin, p.2) :: p.1.1.history))
        (encPair encMe encUnary) encMergeState := by
      fun_prop
    exact (ComputableInPolyTime.optionElimWithInput (encMergeState_pending_polyTime (.fst _ _))
      hnone hsome).of_enc_eq fun q => by dsimp only [mergeStep]; cases q.1.pending <;> rfl
  have hmBranch : ComputableInPolyTime
      (fun q : MergeState × (AMMove × ℕ) => mergeStep q.1 (.merlin, q.2.2))
      encMe encMergeState := by
    dsimp only [mergeStep]
    exact encMergeState_mk_polyTime
      ((ComputableInPolyTime.optionSome encUnary).comp
        (show ComputableInPolyTime
          (fun q : MergeState × (AMMove × ℕ) => q.1.pending.getD 0 + q.2.2)
          encMe encUnary by fun_prop))
      (encMergeState_history_polyTime (.fst _ _))
  exact (computableInPolyTime_amMoveCases
    (m := fun q : MergeState × (AMMove × ℕ) => q.2.1)
    (f := fun q m => mergeStep q.1 (m, q.2.2))
    (by fun_prop) haBranch hmBranch).of_enc_eq fun q => by
    rcases q with ⟨_, ⟨_ | _, _⟩⟩ <;> rfl

/-- `AMGame.mergeMerlin` on a polynomial-time shape is polynomial-time. -/
theorem computableInPolyTime_mergeMerlin {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → List (AMMove × ℕ)} (hg : ComputableInPolyTime g encIn encAMShape) :
    ComputableInPolyTime (fun x => AMGame.mergeMerlin (g x)) encIn encAMShape := by
  have hAccLen : ∀ l : List (AMMove × ℕ),
      (encAMShape l).length ≤ 8 * l.length + 2 * AMGame.transcriptLength l := fun l => by
    induction l with
    | nil => simp [AMGame.transcriptLength]
    | cons y ys ih =>
      have hm1 : (encAMMove y.1).length = 1 := by cases y.1 <;> rfl
      enc_len [encAMShape, hm1, AMGame.transcriptLength, List.map_cons, List.sum_cons] at ih ⊢
  have hspec := ComputableInPolyTime.foldl_spec
    (encB := encMergeState) (encA := encPair encAMMove encUnary) (encL := encAMShape)
    (step := mergeStep) hg (ComputableInPolyTime.const (MergeState.mk none []))
    computableInPolyTime_mergeStep
    (fun _ pre st => st.pending.getD 0 + AMGame.transcriptLength st.history ≤
        AMGame.transcriptLength pre ∧ st.history.length ≤ 2 * pre.length)
    (fun _ => ⟨le_rfl, le_rfl⟩)
    (fun _ pre ⟨opt, acc⟩ ⟨m, n⟩ _ hst => by
      cases m <;> rcases opt with _ | k <;>
        simp only [mergeStep, Option.getD_none, Option.getD_some, zero_add,
          List.length_cons, List.length_append, AMGame.transcriptLength, List.map_cons,
          List.map_append, List.map_nil, List.sum_cons, List.sum_append, List.sum_nil,
          add_zero] at hst ⊢ <;> omega)
    (((PolyBounded.const 24).mul hg.polyBounded_length).add (.const 12))
    (fun x pre st hpre ⟨hsum, hlen⟩ => by
      have hsubT : AMGame.transcriptLength pre ≤ AMGame.transcriptLength (g x) := by
        obtain ⟨_, hsfx⟩ := hpre
        rw [← hsfx]; simp only [AMGame.transcriptLength, List.map_append, List.sum_append]
        exact Nat.le_add_right _ _
      have hgL : pre.length ≤ (encAMShape (g x)).length :=
        hpre.length_le.trans
          (SizedListEncoding.length_le (encA := encPair encAMMove encUnary) (encL := encAMShape) _)
      have hgT : AMGame.transcriptLength pre ≤ (encAMShape (g x)).length :=
        hsubT.trans (AMGame.transcriptLength_le_length_encAMShape (g x))
      have hOptLen : (encOption encUnary st.pending).length ≤ 1 + st.pending.getD 0 := by
        cases st.pending <;> simp
      have hAcc := hAccLen st.history
      simp only [encMergeState_apply, length_encPair]
      omega)
  have hst := hspec.1
  have hoptOut := encMergeState_pending_polyTime hst
  have haccOut := encMergeState_history_polyTime hst
  have hcons : ComputableInPolyTime
      (fun p : γ × ℕ => (AMMove.merlin, p.2) :: ((g p.1).foldl mergeStep ⟨none, []⟩).history)
      (encPair encIn encUnary) encAMShape := by
    have he : ComputableInPolyTime (fun p : γ × ℕ => (AMMove.merlin, p.2))
        (encPair encIn encUnary) (encPair encAMMove encUnary) :=
      (ComputableInPolyTime.const AMMove.merlin).prod (.snd _ _)
    exact he.cons' (haccOut.comp (.fst _ _))
  have hpreRev : ComputableInPolyTime
      (fun x => match ((g x).foldl mergeStep (MergeState.mk none [])).pending with
        | none => ((g x).foldl mergeStep (MergeState.mk none [])).history
        | some m => (.merlin, m) :: ((g x).foldl mergeStep (MergeState.mk none [])).history)
      encIn encAMShape :=
    (ComputableInPolyTime.optionElimWithInput hoptOut haccOut hcons).of_enc_eq fun x => by
      cases ((g x).foldl mergeStep (MergeState.mk none [])).pending <;> rfl
  exact (ComputableInPolyTime.listReverseWithInput hpreRev).of_enc_eq fun x =>
    congrArg encAMShape (by simp only [mergeFlush, mergeMerlin_eq_mergeFlush (g x)])

/-- **Uniform soundness arithmetic for polynomial round counts:** for `1 ≤ c ≤ W` and
`R = 72 * c * W`, `B = R * W`, the soundness factor of `Emulation.three_mul_value_le_one` is
strictly dominated by `(3 / 2) ^ R` for all `n`. -/
theorem six_mul_pow_mul_two_pow_le_three_pow {c W : ℕ} (hc : 1 ≤ c) (hcW : c ≤ W) :
    6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) ^ c * 2 ^ (72 * c * W) ≤
      3 ^ (72 * c * W) := by
  have hW1 : 1 ≤ W := hc.trans hcW
  have hpos : 1 ≤ 72 * c * W * W := by
    have := Nat.mul_le_mul hW1 hW1; nlinarith
  have hbase : 6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) ≤ 2 ^ (40 * W) := by
    have hpowW : W ^ 8 ≤ 2 ^ (8 * W) := by
      calc W ^ 8 ≤ (2 ^ W) ^ 8 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 8
        _ = 2 ^ (8 * W) := by rw [← pow_mul, mul_comm]
    calc 6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2)
        ≤ 6 * (72 * W ^ 2 * (2 * (72 * W * W * W)) ^ 2) := by
          gcongr; exact (by omega : 72 * c * W * W + 1 ≤ 2 * (72 * c * W * W)).trans (by gcongr)
      _ = 6 * (288 * 72 ^ 2) * W ^ 8 := by ring
      _ ≤ 2 ^ 24 * 2 ^ (8 * W) := Nat.mul_le_mul (by norm_num) hpowW
      _ = 2 ^ (24 + 8 * W) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (40 * W) := Nat.pow_le_pow_right two_pos (by omega)
  have hsingle : 6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) * 2 ^ (72 * W) ≤ 3 ^ (72 * W) :=
    calc _ ≤ 2 ^ (40 * W) * 2 ^ (72 * W) := Nat.mul_le_mul_right _ hbase
      _ = (2 ^ 28) ^ (4 * W) := by rw [← pow_add, ← pow_mul]; congr 1; omega
      _ ≤ (3 ^ 18) ^ (4 * W) := Nat.pow_le_pow_left (by norm_num) _
      _ = 3 ^ (72 * W) := by rw [← pow_mul]; congr 1; omega
  calc 6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) ^ c * 2 ^ (72 * c * W)
      ≤ 6 ^ c * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) ^ c * (2 ^ (72 * W)) ^ c := by
        rw [← pow_mul, mul_right_comm 72 W c]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 6))
    _ = (6 * (72 * c ^ 2 * (72 * c * W * W + 1) ^ 2) * 2 ^ (72 * W)) ^ c := by simp only [← mul_pow]
    _ ≤ (3 ^ (72 * W)) ^ c := Nat.pow_le_pow_left hsingle c
    _ = 3 ^ (72 * c * W) := by rw [← pow_mul]; congr 1; ring

end Emulation

/-! ### Dynamic private-coin game classes and `IP[k(n)] ⊆ AM[k(n) + 2]` -/

open IPGame Emulation

/-- `(msg, dec)` is a dynamic private-coin game verifier for `A` with polynomial-time shape `g`
and `ρ(n)` coins evaluated at `n = (enc a).length`. -/
@[expose] def IsIPPolyGameVerifier (enc : α ↪ List Bool) (g : ℕ → List (IPMove × ℕ))
    (ρ : ℕ → ℕ) (msg : α × List Bool × ℕ × List Bool → List Bool)
    (dec : α × List Bool × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 * 2 ^ ρ (enc a).length ≤
      3 * bestCount (fun (c : BitString (ρ (enc a).length)) j p => msg (a, List.ofFn c, j, p))
        (fun (c : BitString (ρ (enc a).length)) t => dec (a, List.ofFn c, t))
        (g (enc a).length)) ∧
    (a ∉ A → 3 * bestCount (fun (c : BitString (ρ (enc a).length)) j p =>
        msg (a, List.ofFn c, j, p))
        (fun (c : BitString (ρ (enc a).length)) t => dec (a, List.ofFn c, t))
        (g (enc a).length) ≤
      2 ^ ρ (enc a).length)

/-- Problems decided by polynomial-time private-coin game verifiers whose move pattern at input
length `n` is `π n`. -/
@[expose] def IPPolyGameClass (enc : α ↪ List Bool) (π : ℕ → List IPMove) : Set (Set α) :=
  {A | ∃ (g : ℕ → List (IPMove × ℕ)) (ρ : ℕ → ℕ)
    (msg : α × List Bool × ℕ × List Bool → List Bool) (dec : α × List Bool × List Bool → Bool),
    (∀ n, (g n).map Prod.fst = π n) ∧
      ComputableInPolyTime g encUnary encIPShape ∧
      ComputableInPolyTime ρ encUnary encUnary ∧
      ComputableInPolyTime msg (encMsgInput enc) encBits ∧
      ComputableInPolyTime dec (encDecInput enc) encBool ∧
      IsIPPolyGameVerifier enc g ρ msg dec A}

/-- `IP[k(n)]` for input-length-dependent alternating move count `k : ℕ → ℕ`, verifier first. -/
@[expose] def IPPolyRounds (enc : α ↪ List Bool) (k : ℕ → ℕ) : Set (Set α) :=
  IPPolyGameClass enc (fun n => (alternatingMoves .arthur (k n)).map AMMove.toIP)

/-- Every fixed-pattern private-coin game class embeds into `IPPolyGameClass`. -/
theorem IPGameClass_subset_IPPolyGameClass {enc : α ↪ List Bool} (π : List IPMove) :
    IPGameClass enc π ⊆ IPPolyGameClass enc (fun _ => π) := by
  rintro A ⟨G, ρ, msg, dec, hG, hmsg, hdec, hA⟩
  refine ⟨evalShape G, fun n => ρ.eval n, msg, dec, fun _ => ?_,
    computableInPolyTime_evalShape G, ComputableInPolyTime.unary_eval ρ, hmsg, hdec, fun a => ?_⟩
  · simp [evalShape, ← hG]
  · simpa [IsIPGameVerifier, countAt] using hA a

/-- Every constant-round `IP[k]` embeds into `IPPolyRounds`. -/
theorem IPk_subset_IPPolyRounds {enc : α ↪ List Bool} (k : ℕ) :
    IPk enc k ⊆ IPPolyRounds enc (fun _ => k) :=
  IPGameClass_subset_IPPolyGameClass _

/-- Public-coin dynamic games embed into private-coin dynamic games with the same move patterns. -/
theorem AMPolyGameClass_subset_IPPolyGameClass {enc : α ↪ List Bool} (π : ℕ → List AMMove) :
    AMPolyGameClass enc π ⊆ IPPolyGameClass enc (fun n => (π n).map AMMove.toIP) := by
  rintro A ⟨g, V, hg, hgp, hV, hA⟩
  have hofAM : ComputableInPolyTime (fun n => ofAM (g n)) encUnary encIPShape :=
    (ComputableInPolyTime.mapWithInput hgp (f := fun _ x => (x.1.toIP, x.2)) <|
      ((show ComputableInPolyTime (fun x : ℕ × (AMMove × ℕ) => x.2.1) _ encAMMove by fun_prop)
        |>.of_enc_eq fun x => by cases x.2.1 <;> rfl).prod (by fun_prop)).of_enc_eq fun _ => rfl
  have htr : ComputableInPolyTime (fun n => AMGame.transcriptLength (g n)) encUnary encUnary :=
    (computableInPolyTime_transcriptLength_dyn hofAM).of_enc_eq fun n => congrArg encUnary (by
      simp [AMGame.transcriptLength, IPGame.transcriptLength, ofAM, List.map_map,
        Function.comp_def])
  refine ⟨fun n => ofAM (g n), fun n => AMGame.transcriptLength (g n),
    fun x => x.2.1.drop x.2.2.2.length, fun x => V (x.1, x.2.2), fun n => ?_,
    hofAM, htr, by fun_prop, hV.comp (by fun_prop), fun a => ?_⟩
  · simp [ofAM, List.map_map, Function.comp_def, ← hg n]
  · set n := (enc a).length
    dsimp only
    rw [bestCount_reveal (g n) (fun t => V (a, t)) rfl,
      transcriptLength_eq_arthurBits_add_merlinBits, pow_add]
    exact ⟨fun ha => by have := Nat.mul_le_mul_right (2 ^ merlinBits (g n)) ((hA a).1 ha); linarith,
      fun ha => by have := Nat.mul_le_mul_right (2 ^ merlinBits (g n)) ((hA a).2 ha); linarith⟩

/-- `AM[k(n)] ⊆ IP[k(n)]`. -/
theorem AMPolyRounds_subset_IPPolyRounds {enc : α ↪ List Bool} (k : ℕ → ℕ) :
    AMPolyRounds enc k ⊆ IPPolyRounds enc k :=
  AMPolyGameClass_subset_IPPolyGameClass _

private theorem alternatingMoves_add_two (x : AMMove) (k : ℕ) :
    alternatingMoves x (k + 2) = x :: x.other :: alternatingMoves x k := by
  cases x <;> rfl

private theorem alternatingMoves_two_mul_add_one (x : AMMove) (m : ℕ) :
    alternatingMoves x (2 * m + 1) = alternatingMoves x (2 * m) ++ [x] := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
      show 2 * (m + 1) = 2 * m + 2 by omega,
      alternatingMoves_add_two, alternatingMoves_add_two, ih]
    rfl

private theorem length_alternatingMoves (x : AMMove) (k : ℕ) :
    (alternatingMoves x k).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [alternatingMoves, ih]

private theorem list_take_append_getLastD {β : Type} (l : List β) (d : β) (hl : l ≠ []) :
    l.take (l.length - 1) ++ [l.getLastD d] = l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys => simpa [List.take_succ_cons, List.getLastD_cons] using ih (by simp)

private theorem list_getLastD_map_fst (l : List (IPMove × ℕ)) (d : IPMove × ℕ) (hl : l ≠ []) :
    (l.getLastD d).1 = (l.map Prod.fst).getLastD d.1 := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys => simpa using ih (by simp)

private theorem computableInPolyTime_appendMsgDec {enc : α ↪ List Bool}
    {L j : α × List Bool × List Bool → ℕ}
    {msg : α × List Bool × ℕ × List Bool → List Bool}
    {dec : α × List Bool × List Bool → Bool}
    (hL : ComputableInPolyTime L (encDecInput enc) encUnary)
    (hj : ComputableInPolyTime j (encDecInput enc) encUnary)
    (hmsg : ComputableInPolyTime msg (encMsgInput enc) encBits)
    (hdec : ComputableInPolyTime dec (encDecInput enc) encBool) :
    ComputableInPolyTime (fun x => dec (x.1, x.2.1, x.2.2 ++ BitString.listRow (L x) 0
      (msg (x.1, x.2.1, j x, x.2.2)))) (encDecInput enc) encBool :=
  have ha : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.1)
      (encDecInput enc) enc := .fst _ _
  have hc : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.1)
      (encDecInput enc) encBits := (ComputableInPolyTime.snd _ _).fst'
  have ht : ComputableInPolyTime (fun x : α × List Bool × List Bool => x.2.2)
      (encDecInput enc) encBits := (ComputableInPolyTime.snd _ _).snd'
  hdec.comp (ha.prod (hc.prod (ht.bitsAppend
    (hL.bitsRowWithInput (.const 0) (hmsg.comp (ha.prod (hc.prod (hj.prod ht))))))))

/-- For constant `q`, dropping the trailing verifier move gives `IP[2 * q + 1] = IP[2 * q]`. -/
theorem IPk_two_mul_add_one_eq {enc : α ↪ List Bool} (q : ℕ) :
    IPk enc (2 * q + 1) = IPk enc (2 * q) := by
  refine le_antisymm ?_ ?_
  · rintro A ⟨G, ρ, msg, dec, hG, hmsg, hdec, hA⟩
    have hpat : G.map Prod.fst =
        (alternatingMoves .arthur (2 * q)).map AMMove.toIP ++ [.verifier] := by
      rw [hG, alternatingMoves_two_mul_add_one, List.map_append]; rfl
    obtain ⟨G', Gtail, rfl, hG', htail⟩ := List.map_eq_append_iff.1 hpat
    obtain ⟨⟨v, L⟩, Gnil, rfl, hv, hnil⟩ := List.map_eq_cons_iff.1 htail
    subst hv; obtain rfl : Gnil = [] := List.map_eq_nil_iff.1 hnil
    refine ⟨G', ρ, msg,
      fun x => dec (x.1, x.2.1, x.2.2 ++ BitString.listRow (L.eval (enc x.1).length) 0
        (msg (x.1, x.2.1, G'.length, x.2.2))), hG', hmsg,
      computableInPolyTime_appendMsgDec
        ((ComputableInPolyTime.unary_eval L).comp
          ((ComputableInPolyTime.encoding_length enc).comp (.fst _ _)))
        (.const G'.length) hmsg hdec,
      fun a => ?_⟩
    have hlenG : (evalShape G' (enc a).length).length = G'.length := by simp [evalShape]
    have hha := hA a
    dsimp only [countAt] at hha ⊢
    rw [evalShape_append, evalShape_cons, evalShape_nil, bestCount_append_verifier, hlenG] at hha
    simpa only [BitString.listRow_zero] using hha
  · rintro A ⟨G, ρ, msg, dec, hG, hmsg, hdec, hA⟩
    refine ⟨G ++ [(.verifier, 0)], ρ, msg, dec, ?_, hmsg, hdec, fun a => ?_⟩
    · rw [List.map_append, hG, alternatingMoves_two_mul_add_one, List.map_append]; rfl
    · simpa [countAt, evalShape_append, evalShape_cons, evalShape_nil,
        bestCount_append_verifier] using hA a

private theorem map_fst_mergeMerlin_emulation (B Z ρ : ℕ) :
    ∀ (m : ℕ) (g : List (IPMove × ℕ)),
      g.map Prod.fst = (alternatingMoves .arthur (2 * m)).map AMMove.toIP →
      (AMGame.mergeMerlin (shape B Z (g ++ [(.verifier, ρ)]))).map Prod.fst =
        alternatingMoves .arthur (2 * m + 2) := by
  intro m
  induction m with
  | zero =>
    intro g hg
    obtain rfl : g = [] := List.map_eq_nil_iff.1 hg
    rfl
  | succ m ih =>
    intro g hg
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, alternatingMoves_add_two, List.map_cons,
      List.map_cons] at hg
    dsimp only [AMMove.other, AMMove.toIP] at hg
    rw [show 2 * (m + 1) = 2 * m + 2 by omega]
    obtain ⟨⟨_, nV⟩, g₁, rfl, rfl, hg₁⟩ := List.map_eq_cons_iff.1 hg
    obtain ⟨⟨_, nP⟩, g', rfl, rfl, hg'⟩ := List.map_eq_cons_iff.1 hg₁
    have ih' := ih g' hg'
    rcases h : AMGame.mergeMerlin (shape B Z (g' ++ [(.verifier, ρ)])) with _ | ⟨⟨_ | _, nA⟩, tail⟩
    · simp [h, alternatingMoves] at ih'
    · simp only [List.cons_append, shape, AMGame.mergeMerlin, h, List.map_cons]
      change _ = .arthur :: .merlin :: alternatingMoves .arthur (2 * m + 2)
      rw [← ih', h]
      rfl
    · simp [h, alternatingMoves] at ih'

private def truncShape (g₀ : ℕ → List (IPMove × ℕ)) (n : ℕ) : List (IPMove × ℕ) :=
  if (g₀ n).length % 2 = 1 then (g₀ n).take ((g₀ n).length - 1) else g₀ n

private theorem computableInPolyTime_truncShape {g₀ : ℕ → List (IPMove × ℕ)}
    (hgp₀ : ComputableInPolyTime g₀ encUnary encIPShape) :
    ComputableInPolyTime (truncShape g₀) encUnary encIPShape :=
  have hlen : ComputableInPolyTime (fun n => (g₀ n).length) encUnary encUnary :=
    (ComputableInPolyTime.length_list (encPair encIPMove encUnary)).comp hgp₀
  ((computableInPolyTime_unaryOdd hlen).ite
    (ComputableInPolyTime.listTakeWithInput hgp₀ (hlen.unary_sub' (.const 1))) hgp₀).of_enc_eq
    fun n => by simp only [truncShape, decide_eq_true_eq]

private def truncDec (enc : α ↪ List Bool) (g₀ : ℕ → List (IPMove × ℕ))
    (msg₀ : α × List Bool × ℕ × List Bool → List Bool)
    (dec₀ : α × List Bool × List Bool → Bool) (x : α × List Bool × List Bool) : Bool :=
  let n := (enc x.1).length
  if (g₀ n).length % 2 = 1 then
    dec₀ (x.1, x.2.1, x.2.2 ++ BitString.listRow ((g₀ n).getLastD (.verifier, 0)).2 0
      (msg₀ (x.1, x.2.1, (g₀ n).length - 1, x.2.2)))
  else dec₀ x

private theorem computableInPolyTime_truncDec {enc : α ↪ List Bool} {g₀ : ℕ → List (IPMove × ℕ)}
    {msg₀ : α × List Bool × ℕ × List Bool → List Bool} {dec₀ : α × List Bool × List Bool → Bool}
    (hgp₀ : ComputableInPolyTime g₀ encUnary encIPShape)
    (hmsg₀ : ComputableInPolyTime msg₀ (encMsgInput enc) encBits)
    (hdec₀ : ComputableInPolyTime dec₀ (encDecInput enc) encBool) :
    ComputableInPolyTime (truncDec enc g₀ msg₀ dec₀) (encDecInput enc) encBool := by
  have hg₀n := hgp₀.comp ((ComputableInPolyTime.encoding_length enc).comp
    (.fst enc (encPair encBits encBits)))
  have hlen := (ComputableInPolyTime.length_list (encPair encIPMove encUnary)).comp hg₀n
  have hsub := hlen.unary_sub' (.const 1)
  have hlast : ComputableInPolyTime (fun x : α × List Bool × List Bool =>
      ((g₀ (enc x.1).length).getLastD (.verifier, 0)).2) (encDecInput enc) encUnary :=
    ((ComputableInPolyTime.snd encIPMove encUnary).comp
      (ComputableInPolyTime.listGetDWithInput hg₀n hsub (.verifier, 0))).of_enc_eq fun x =>
        congrArg encUnary <| by
          rw [Function.comp_apply, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]; rfl
  exact ((computableInPolyTime_unaryOdd hlen).ite
    (computableInPolyTime_appendMsgDec hlast hsub hmsg₀ hdec₀) hdec₀).of_enc_eq fun x => by
    simp only [truncDec, decide_eq_true_eq, Function.comp_apply]

private def gsC (g₁ : ℕ → List (IPMove × ℕ)) (n : ℕ) : ℕ := verifierMoves (g₁ n) + 1

private def gsW (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : ℕ :=
  transcriptLength (g₁ n) + (g₁ n).length + ρ₀ n + 1

private def gsR (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : ℕ :=
  72 * gsC g₁ n * gsW g₁ ρ₀ n

private def gsB (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : ℕ :=
  gsR g₁ ρ₀ n * gsW g₁ ρ₀ n

private def gsZ (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * (gsB g₁ ρ₀ n + 6 * gsC g₁ n * (gsB g₁ ρ₀ n + 1))

private def gsK (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : ℕ :=
  Emulation.threshold (gsC g₁ n) (gsB g₁ ρ₀ n)

private def gsRep (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : List (IPMove × ℕ) :=
  repeatShape (gsR g₁ ρ₀ n) (g₁ n) ++ [(.verifier, gsR g₁ ρ₀ n * ρ₀ n)]

private def gsAM (g₀ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ) (n : ℕ) : List (AMMove × ℕ) :=
  let g₁ := truncShape g₀
  let base := AMGame.mergeMerlin (shape (gsB g₁ ρ₀ n) (gsZ g₁ ρ₀ n) (gsRep g₁ ρ₀ n))
  if (g₀ n).length % 2 = 1 then base ++ [(.arthur, 0)] else base

private def gsMsgRep (enc : α ↪ List Bool) (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ)
    (msg₀ : α × List Bool × ℕ × List Bool → List Bool) (R : ℕ → ℕ)
    (a : α) (c' : List Bool) (j : ℕ) (p : List Bool) : List Bool :=
  repeatMsg (R (enc a).length) (g₁ (enc a).length)
    (fun i j' p' => msg₀ (a, BitString.listRow (ρ₀ (enc a).length) i c', j', p')) j p

private def gsDecRep (enc : α ↪ List Bool) (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ)
    (dec₁ : α × List Bool × List Bool → Bool) (R : ℕ → ℕ)
    (a : α) (c' : List Bool) (t : List Bool) : Bool :=
  repeatDec (R (enc a).length) (g₁ (enc a).length)
    (fun i t' => dec₁ (a, BitString.listRow (ρ₀ (enc a).length) i c', t')) t

private def gsReveal (enc : α ↪ List Bool) (g₁ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ)
    (msg₀ : α × List Bool × ℕ × List Bool → List Bool)
    (dec₁ : α × List Bool × List Bool → Bool) (R : ℕ → ℕ) (a : α) (w : List Bool) : Bool :=
  revealPayoff (gsMsgRep enc g₁ ρ₀ msg₀ R a) (gsDecRep enc g₁ ρ₀ dec₁ R a)
    (repeatShape (R (enc a).length) (g₁ (enc a).length))
    (transcriptLength (repeatShape (R (enc a).length) (g₁ (enc a).length))) w

private def gsVAM (enc : α ↪ List Bool) (g₀ : ℕ → List (IPMove × ℕ)) (ρ₀ : ℕ → ℕ)
    (msg₀ : α × List Bool × ℕ × List Bool → List Bool)
    (dec₀ : α × List Bool × List Bool → Bool) (x : α × List Bool) : Bool :=
  check
    (gsB (truncShape g₀) ρ₀ (enc x.1).length)
    (gsZ (truncShape g₀) ρ₀ (enc x.1).length)
    (gsK (truncShape g₀) ρ₀ (enc x.1).length)
    (gsReveal enc (truncShape g₀) ρ₀ msg₀ (truncDec enc g₀ msg₀ dec₀)
      (gsR (truncShape g₀) ρ₀) x.1)
    (gsRep (truncShape g₀) ρ₀ (enc x.1).length)
    (gsR (truncShape g₀) ρ₀ (enc x.1).length * ρ₀ (enc x.1).length -
      gsR (truncShape g₀) ρ₀ (enc x.1).length)
    [] x.2

private theorem computableInPolyTime_gsC {g₁ : ℕ → List (IPMove × ℕ)}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape) :
    ComputableInPolyTime (gsC g₁) encUnary encUnary := by
  have := computableInPolyTime_verifierMoves_dyn hg₁; unfold gsC; fun_prop

private theorem computableInPolyTime_gsW {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsW g₁ ρ₀) encUnary encUnary := by
  have := computableInPolyTime_transcriptLength_dyn hg₁; unfold gsW; fun_prop

private theorem computableInPolyTime_gsR {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsR g₁ ρ₀) encUnary encUnary := by
  have := computableInPolyTime_gsC hg₁; have := computableInPolyTime_gsW hg₁ hρ
  unfold gsR; fun_prop

private theorem computableInPolyTime_gsB {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsB g₁ ρ₀) encUnary encUnary := by
  have := computableInPolyTime_gsR hg₁ hρ; have := computableInPolyTime_gsW hg₁ hρ
  unfold gsB; fun_prop

private theorem computableInPolyTime_gsZ {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsZ g₁ ρ₀) encUnary encUnary := by
  have := computableInPolyTime_gsC hg₁; have := computableInPolyTime_gsB hg₁ hρ
  unfold gsZ; fun_prop

private theorem computableInPolyTime_gsK {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsK g₁ ρ₀) encUnary encUnary := by
  have := computableInPolyTime_gsC hg₁; have := computableInPolyTime_gsB hg₁ hρ
  unfold gsK Emulation.threshold; fun_prop

private theorem computableInPolyTime_gsRep {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsRep g₁ ρ₀) encUnary encIPShape := by
  have := computableInPolyTime_gsR hg₁ hρ
  have := computableInPolyTime_repeatShape_dyn this hg₁
  unfold gsRep; fun_prop

private theorem computableInPolyTime_gsAM {g₀ : ℕ → List (IPMove × ℕ)} {ρ₀ : ℕ → ℕ}
    (hgp₀ : ComputableInPolyTime g₀ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary) :
    ComputableInPolyTime (gsAM g₀ ρ₀) encUnary encAMShape := by
  have hg₁ := computableInPolyTime_truncShape hgp₀
  have hbase := computableInPolyTime_mergeMerlin
    (computableInPolyTime_shape_dyn (computableInPolyTime_gsB hg₁ hρ)
      (computableInPolyTime_gsZ hg₁ hρ) (computableInPolyTime_gsRep hg₁ hρ))
  exact ((computableInPolyTime_unaryOdd (by fun_prop :
      ComputableInPolyTime (fun n => (g₀ n).length) encUnary encUnary)).ite
    (ComputableInPolyTime.listAppend' hbase (ComputableInPolyTime.const [(.arthur, 0)]))
    hbase).of_enc_eq fun n => by simp [gsAM]

private theorem computableInPolyTime_gsReveal {enc : α ↪ List Bool}
    {g₁ : ℕ → List (IPMove × ℕ)} {ρ₀ R : ℕ → ℕ}
    {msg₀ : α × List Bool × ℕ × List Bool → List Bool}
    {dec₁ : α × List Bool × List Bool → Bool} {q : α × List Bool → List Bool}
    (hg₁ : ComputableInPolyTime g₁ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary)
    (hR : ComputableInPolyTime R encUnary encUnary)
    (hmsg₀ : ComputableInPolyTime msg₀ (encMsgInput enc) encBits)
    (hdec₁ : ComputableInPolyTime dec₁ (encDecInput enc) encBool)
    (hq : ComputableInPolyTime q (encPair enc encBits) encBits) :
    ComputableInPolyTime (fun x : α × List Bool => gsReveal enc g₁ ρ₀ msg₀ dec₁ R x.1 (q x))
      (encPair enc encBits) encBool := by
  have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary := (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  have haM : ComputableInPolyTime (fun y : α × List Bool × ℕ × List Bool => y.1)
      (encMsgInput enc) enc := .fst _ _
  have hnM := (ComputableInPolyTime.encoding_length enc).comp haM
  have hmsgRep : ComputableInPolyTime
      (fun y : α × List Bool × ℕ × List Bool => gsMsgRep enc g₁ ρ₀ msg₀ R y.1 y.2.1 y.2.2.1 y.2.2.2)
      (encMsgInput enc) encBits :=
    (computableInPolyTime_repeatMsg_dyn haM ((ComputableInPolyTime.snd _ _).fst')
      (hg₁.comp hnM) (hR.comp hnM) (hρ.comp hnM)
      ((ComputableInPolyTime.snd _ _).snd'.fst') ((ComputableInPolyTime.snd _ _).snd'.snd')
      hmsg₀).of_enc_eq fun _ => rfl
  have haD : ComputableInPolyTime (fun y : α × List Bool × List Bool => y.1)
      (encDecInput enc) enc := .fst _ _
  have hnD := (ComputableInPolyTime.encoding_length enc).comp haD
  have hdecRep : ComputableInPolyTime
      (fun y : α × List Bool × List Bool => gsDecRep enc g₁ ρ₀ dec₁ R y.1 y.2.1 y.2.2)
      (encDecInput enc) encBool :=
    (computableInPolyTime_repeatDec_dyn haD ((ComputableInPolyTime.snd _ _).fst')
      (hg₁.comp hnD) (hR.comp hnD) (hρ.comp hnD)
      ((ComputableInPolyTime.snd _ _).snd') hdec₁).of_enc_eq fun _ => rfl
  have hgrepx := computableInPolyTime_repeatShape_dyn (hR.comp hn) (hg₁.comp hn)
  exact computableInPolyTime_revealPayoff_dyn (.fst _ _) hgrepx
    (computableInPolyTime_transcriptLength_dyn hgrepx) hmsgRep hdecRep hq

private theorem computableInPolyTime_gsVAM {enc : α ↪ List Bool} {g₀ : ℕ → List (IPMove × ℕ)}
    {ρ₀ : ℕ → ℕ} {msg₀ : α × List Bool × ℕ × List Bool → List Bool}
    {dec₀ : α × List Bool × List Bool → Bool}
    (hgp₀ : ComputableInPolyTime g₀ encUnary encIPShape)
    (hρ : ComputableInPolyTime ρ₀ encUnary encUnary)
    (hmsg₀ : ComputableInPolyTime msg₀ (encMsgInput enc) encBits)
    (hdec₀ : ComputableInPolyTime dec₀ (encDecInput enc) encBool) :
    ComputableInPolyTime (gsVAM enc g₀ ρ₀ msg₀ dec₀) (encPair enc encBits) encBool := by
  have hg₁ := computableInPolyTime_truncShape hgp₀
  have hdec₁ := computableInPolyTime_truncDec hgp₀ hmsg₀ hdec₀
  have hR := computableInPolyTime_gsR hg₁ hρ
  have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary := (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  exact computableInPolyTime_check_dyn ((computableInPolyTime_gsB hg₁ hρ).comp hn)
    ((computableInPolyTime_gsZ hg₁ hρ).comp hn) ((computableInPolyTime_gsK hg₁ hρ).comp hn)
    ((computableInPolyTime_gsRep hg₁ hρ).comp hn)
    (fun {q} hq => computableInPolyTime_gsReveal hg₁ hρ hR hmsg₀ hdec₁ hq)
    (((hR.comp hn).unary_mul' (hρ.comp hn)).unary_sub' (hR.comp hn))
    (.const []) (.snd _ _)

private theorem truncShape_map_fst {g₀ : ℕ → List (IPMove × ℕ)} {k : ℕ → ℕ}
    (hg₀ : ∀ n, (g₀ n).map Prod.fst = (alternatingMoves .arthur (k n)).map AMMove.toIP) (n : ℕ) :
    (truncShape g₀ n).map Prod.fst =
      (alternatingMoves .arthur (2 * (k n / 2))).map AMMove.toIP := by
  have hlen : (g₀ n).length = k n := by
    simpa only [List.length_map, length_alternatingMoves] using congrArg List.length (hg₀ n)
  by_cases hodd : k n % 2 = 1
  · have hodd' : (g₀ n).length % 2 = 1 := by omega
    have halt : alternatingMoves .arthur (k n) =
        alternatingMoves .arthur (2 * (k n / 2)) ++ [.arthur] := by
      conv_lhs => rw [show k n = 2 * (k n / 2) + 1 by omega]
      exact alternatingMoves_two_mul_add_one .arthur (k n / 2)
    simp only [truncShape, hodd', ite_true, List.map_take, hg₀ n, halt, List.map_append]
    rw [show (g₀ n).length - 1 = 2 * (k n / 2) by omega,
      List.take_left' (by simp [length_alternatingMoves])]
  · have hodd' : ¬(g₀ n).length % 2 = 1 := by omega
    rw [truncShape, ite_eq_right hodd', hg₀ n]
    congr 2; omega

private theorem bestCount_truncDec {enc : α ↪ List Bool} {g₀ : ℕ → List (IPMove × ℕ)}
    {k ρ₀ : ℕ → ℕ} (msg₀ : α × List Bool × ℕ × List Bool → List Bool)
    (dec₀ : α × List Bool × List Bool → Bool)
    (hg₀ : ∀ n, (g₀ n).map Prod.fst = (alternatingMoves .arthur (k n)).map AMMove.toIP) (a : α) :
    bestCount (fun (c : BitString (ρ₀ (enc a).length)) j p => msg₀ (a, List.ofFn c, j, p))
        (fun (c : BitString (ρ₀ (enc a).length)) t =>
          truncDec enc g₀ msg₀ dec₀ (a, List.ofFn c, t)) (truncShape g₀ (enc a).length) =
      bestCount (fun (c : BitString (ρ₀ (enc a).length)) j p => msg₀ (a, List.ofFn c, j, p))
        (fun (c : BitString (ρ₀ (enc a).length)) t => dec₀ (a, List.ofFn c, t))
        (g₀ (enc a).length) := by
  set n := (enc a).length
  have hlen : (g₀ n).length = k n := by
    simpa only [List.length_map, length_alternatingMoves] using congrArg List.length (hg₀ n)
  by_cases hodd : (g₀ n).length % 2 = 1
  · have hne : g₀ n ≠ [] := by intro h; simp [h] at hodd
    have hlastMove : ((g₀ n).getLastD (.verifier, 0)).1 = .verifier := by
      rw [list_getLastD_map_fst _ _ hne, hg₀ n]
      conv_lhs => rw [show k n = 2 * (k n / 2) + 1 by omega]
      rw [alternatingMoves_two_mul_add_one, List.map_append]
      simp [AMMove.toIP]
    have hpair : (g₀ n).getLastD (.verifier, 0) =
        (.verifier, ((g₀ n).getLastD (.verifier, 0)).2) := Prod.ext hlastMove rfl
    have hsplit : g₀ n = truncShape g₀ n ++ [(.verifier, ((g₀ n).getLastD (.verifier, 0)).2)] := by
      dsimp only [truncShape]; rw [ite_eq_left hodd, ← hpair]
      exact (list_take_append_getLastD (g₀ n) (.verifier, 0) hne).symm
    conv_rhs => rw [hsplit, bestCount_append_verifier]
    refine congrArg (fun f => bestCount _ f _) (funext₂ fun c t => ?_)
    dsimp only [truncDec]
    have hlt : (truncShape g₀ n).length = (g₀ n).length - 1 := by
      simp only [truncShape, hodd, ite_true, List.length_take]; omega
    rw [ite_eq_left hodd, BitString.listRow_zero, hlt]
  · simp only [truncShape, truncDec, n, hodd, ↓reduceIte]

private theorem gsAM_map_fst {g₀ : ℕ → List (IPMove × ℕ)} {k : ℕ → ℕ} (ρ₀ : ℕ → ℕ)
    (hg₀ : ∀ n, (g₀ n).map Prod.fst = (alternatingMoves .arthur (k n)).map AMMove.toIP) (n : ℕ) :
    (gsAM g₀ ρ₀ n).map Prod.fst = alternatingMoves .arthur (k n + 2) := by
  have hlen : (g₀ n).length = k n := by
    simpa only [List.length_map, length_alternatingMoves] using congrArg List.length (hg₀ n)
  have hbase : (AMGame.mergeMerlin (shape (gsB (truncShape g₀) ρ₀ n) (gsZ (truncShape g₀) ρ₀ n)
      (gsRep (truncShape g₀) ρ₀ n))).map Prod.fst = alternatingMoves .arthur (2 * (k n / 2) + 2) :=
    map_fst_mergeMerlin_emulation (gsB (truncShape g₀) ρ₀ n) (gsZ (truncShape g₀) ρ₀ n)
      (gsR (truncShape g₀) ρ₀ n * ρ₀ n) (k n / 2)
      (repeatShape (gsR (truncShape g₀) ρ₀ n) (truncShape g₀ n))
      (by simp [repeatShape, List.map_map, Function.comp_def, truncShape_map_fst hg₀ n])
  by_cases hodd : (g₀ n).length % 2 = 1
  · simp only [gsAM, hodd, ↓reduceIte, List.map_append, List.map_singleton, hbase]
    rw [show k n + 2 = 2 * (k n / 2 + 1) + 1 by omega, alternatingMoves_two_mul_add_one,
      show 2 * (k n / 2 + 1) = 2 * (k n / 2) + 2 by omega]
  · simp only [gsAM, hodd, ↓reduceIte, hbase]
    congr 1
    omega

/-- **Goldwasser–Sipser for polynomially many rounds (`IP[k(n)] ⊆ AM[k(n) + 2]`)** without
round collapse: odd-length patterns drop their trailing verifier move into `dec`, while parallel
repetition of `R(n) = 72 * c(n) * W(n)` copies beats `μ ^ c(n)` uniformly for all `n`. -/
theorem IPPolyRounds_subset_AMPolyRounds {enc : α ↪ List Bool} (k : ℕ → ℕ) :
    IPPolyRounds enc k ⊆ AMPolyRounds enc (fun n => k n + 2) := by
  rintro A ⟨g₀, ρ₀, msg₀, dec₀, hg₀, hgp₀, hρp₀, hmsg₀, hdec₀, hA⟩
  refine ⟨gsAM g₀ ρ₀, gsVAM enc g₀ ρ₀ msg₀ dec₀, gsAM_map_fst ρ₀ hg₀,
    computableInPolyTime_gsAM hgp₀ hρp₀, computableInPolyTime_gsVAM hgp₀ hρp₀ hmsg₀ hdec₀, ?_⟩
  rw [isAMPolyGameVerifier_iff_value]
  intro a
  set g₁ := truncShape g₀; set dec₁ := truncDec enc g₀ msg₀ dec₀; set n := (enc a).length
  set R := gsR g₁ ρ₀ n; set B := gsB g₁ ρ₀ n; set Z := gsZ g₁ ρ₀ n
  set rep := gsRep g₁ ρ₀ n; set rev := gsReveal enc g₁ ρ₀ msg₀ dec₁ (gsR g₁ ρ₀) a
  have hvalAM : ∀ f : List Bool → ℚ, AMGame.value true (gsAM g₀ ρ₀ n) f =
      AMGame.value true (shape B Z rep) f := fun f => by
    dsimp only [gsAM]
    split_ifs
    · rw [AMGame.value_append_arthur_zero, AMGame.value_mergeMerlin]
    · exact AMGame.value_mergeMerlin _ _
  have hc_eq : verifierMoves rep = gsC g₁ n := by
    simp [rep, gsRep, gsC, verifierMoves, repeatShape, List.map_append, List.map_map,
      Function.comp_def]
  have hcpos : 0 < verifierMoves rep := by rw [hc_eq]; dsimp [gsC]; omega
  have hW_ge : gsC g₁ n ≤ gsW g₁ ρ₀ n := by
    have hvm : verifierMoves (g₁ n) ≤ (g₁ n).length := by
      simpa [verifierMoves, List.length_map] using
        List.count_le_length (a := IPMove.verifier) (l := (g₁ n).map Prod.fst)
    dsimp [gsC, gsW]; omega
  have hg_bits : verifierBits rep ≤ B := by
    dsimp only [rep, gsRep, B, gsB]
    rw [verifierBits_append, verifierBits_repeatShape, verifierBits_verifier,
      show verifierBits [] = 0 from rfl, Nat.add_zero, ← Nat.mul_add]
    have := verifierBits_le_transcriptLength (g₁ n)
    exact Nat.mul_le_mul_left _ (by dsimp [gsW]; omega)
  have hκ_le : R * ρ₀ n - R ≤ B :=
    (Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ (by dsimp [gsB, gsW]; omega))
  set N₀ := bestCount (fun (c' : BitString (ρ₀ n)) j p => msg₀ (a, List.ofFn c', j, p))
    (fun (c' : BitString (ρ₀ n)) t => dec₁ (a, List.ofFn c', t)) (g₁ n)
  have hN_eq : countFrom rep rev [] = N₀ ^ R := by
    change countFrom (repeatShape R (g₁ n) ++ [(.verifier, R * ρ₀ n)])
      (revealPayoff (gsMsgRep enc g₁ ρ₀ msg₀ (gsR g₁ ρ₀) a)
        (gsDecRep enc g₁ ρ₀ dec₁ (gsR g₁ ρ₀) a)
        (repeatShape R (g₁ n)) (transcriptLength (repeatShape R (g₁ n)))) [] = _
    rw [countFrom_revealPayoff _ _ _ rfl _]
    exact bestCount_repeat R (ρ₀ n)
      (fun c' j p => msg₀ (a, c', j, p)) (fun c' t => dec₁ (a, c', t)) (g₁ n)
  have ⟨h1, h2⟩ := hA a
  rw [← bestCount_truncDec msg₀ dec₀ hg₀ a] at h1 h2
  dsimp only [gsVAM]
  simp only [hvalAM]
  rw [show gsK g₁ ρ₀ n = Emulation.threshold (verifierMoves rep) B by simp [gsK, hc_eq, B]]
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · refine two_le_three_mul_value B Z rev rep hcpos (by simp [Z, gsZ, hc_eq, B])
      hg_bits (R * ρ₀ n - R) hκ_le ?_
    rw [hN_eq]
    refine two_pow_sub_le ?_
    calc 2 ^ R * 2 ^ (R * ρ₀ n) = (2 * 2 ^ ρ₀ n) ^ R := by rw [mul_pow, pow_mul']
      _ ≤ (3 * N₀) ^ R := Nat.pow_le_pow_left (h1 ha) _
      _ = 3 ^ R * N₀ ^ R := mul_pow _ _ _
  · refine three_mul_value_le_one B Z rev rep hcpos (R * ρ₀ n - R) hκ_le ?_
    rw [hN_eq]
    refine le_two_pow_sub ?_
    have hgap : 6 * (72 * verifierMoves rep ^ 2 * (B + 1) ^ 2) ^ verifierMoves rep * 2 ^ R ≤
        3 ^ R := hc_eq ▸ six_mul_pow_mul_two_pow_le_three_pow (by dsimp [gsC]; omega) hW_ge
    calc 6 * (72 * verifierMoves rep ^ 2 * (B + 1) ^ 2) ^ verifierMoves rep * N₀ ^ R * 2 ^ R
        = 6 * (72 * verifierMoves rep ^ 2 * (B + 1) ^ 2) ^ verifierMoves rep * 2 ^ R * N₀ ^ R := by
          ring
      _ ≤ 3 ^ R * N₀ ^ R := Nat.mul_le_mul_right _ hgap
      _ = (3 * N₀) ^ R := (mul_pow _ _ _).symm
      _ ≤ (2 ^ ρ₀ n) ^ R := Nat.pow_le_pow_left (h2 ha) _
      _ = 2 ^ (R * ρ₀ n) := by rw [← pow_mul, mul_comm]

end Cslib.Complexity
