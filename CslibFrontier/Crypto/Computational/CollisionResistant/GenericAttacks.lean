/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Unpair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Sqrt
import CslibFrontier.Foundations.Data.BitString.WordsOfLength
import CslibFrontier.Languages.Probabilistic.Repeat
import CslibFrontier.Probability.IID.FunctionCollision
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Brute force and the birthday attack as polynomial-time collision finders

The generic collision attacks of [BonehShoup2023], §8.3 (printed pp. 293–295), brute force and
Algorithm BirthdayAttack, as word-level `CollisionFinder`s with `IsPPT` certificates, and the
refutations of `CollisionResistantOn` they give.
`CslibFrontier.Crypto.Computational.CollisionResistant.Birthday` instead treats the birthday finder
as an oracle program and counts its oracle calls; here each finder is a probabilistic
polynomial-time program that evaluates the keyed hash itself.

`collidingPairList? h ms` is the first pair of different messages of `ms` with equal digests. Brute
force (`bruteForceCollisionFinder`) searches a fixed list of more than `2 ^ ℓ(n)` distinct valid
messages and always succeeds; the birthday finder (`birthdayCollisionFinder`) with the book's
`⌈2 √N⌉ + 1` samples, `N = 2 ^ ℓ(n)`, succeeds with probability at least `1/2` when
`100 N ≤ 2 ^ msgLen(n)` and `valid` accepts every `msgLen(n)`-bit message (Lemma 8.2).

Every refutation needs `2 ^ ℓ(n)` to be polynomial in `n` (the birthday statements and
`not_collisionResistant_of_two_pow_polyTime` assume that it is computable in unary in polynomial
time), so they cover constant and logarithmic digest lengths, where brute force alone refutes
collision resistance; the birthday refutation adds a certified finder with success `1/2` on
`msgLen(n)`-bit messages. Nothing compares the `√N` samples with the `N + 1` messages of brute force
in machine time. The `2 ^ ℓ + 1` hash evaluations of brute force are not counted; the oracle-call
count of `Birthday.lean` is for the birthday finder.

## Differences from [BonehShoup2023]

* The statements are asymptotic: `n`-bit keys, `ℓ(n)`-bit digests, `msgLen(n)`-bit messages, and
  the domain predicate `valid` must accept the messages searched (`hvalid`). `|M| ≥ 100 N` becomes
  `100 * 2 ^ ℓ n ≤ 2 ^ msgLen n`.
* Steps 4 and 5 of Algorithm BirthdayAttack test for equal digests, then for different messages;
  `collidingPairList?`, like `collidingPair?`, tests both at once, so the finder succeeds on the
  event of Lemma 8.2. When it finds nothing, its output `([], [])` is not a collision.
* Brute force searches any polynomial-time list of more than `2 ^ ℓ(n)` distinct messages;
  `not_collisionResistant_of_two_pow_polyTime` uses the book's `2 ^ ℓ(n) + 1`.

## Main definitions

* `Cslib.Crypto.collidingPairList?`, `Cslib.Crypto.bruteForceCollisionFinder`,
  `Cslib.Crypto.birthdayCollisionFinder`.

## Main results

* `Cslib.Crypto.isSome_collidingPairList?_of_two_pow_lt`: the pigeonhole step of brute force.
* `Cslib.Crypto.succProbability_bruteForceCollisionFinder`,
  `Cslib.Crypto.half_le_succProbability_birthdayCollisionFinder`: success `1` and `≥ 1/2`.
* `Cslib.Crypto.not_collisionResistantOn_of_bruteForce`,
  `Cslib.Crypto.not_collisionResistantOn_of_birthday`: the refutations.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], §8.3 (printed pp. 293–295).
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM Cslib.Probability
open scoped ENNReal NNReal

section Search

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The first pair of different messages of `ms` with equal digests under `h`, in the order of the
pairs of `ms.map fun m => (m, h m)` with itself, so that each digest is computed once. This is the
list form of `collidingPair?`. -/
@[expose] def collidingPairList? (h : α → β) (ms : List α) : Option (α × α) :=
  let ds := ms.map fun m => (m, h m)
  ((ds ×ˢ ds).find? fun ((a, da), (b, db)) => da = db ∧ a ≠ b).map fun ((a, _), (b, _)) => (a, b)

/-- An output `some (a, b)` of `collidingPairList?` is a collision among the messages. -/
theorem collidingPairList?_eq_some {h : α → β} {ms : List α} {a b : α}
    (hab : collidingPairList? h ms = some (a, b)) :
    a ∈ ms ∧ b ∈ ms ∧ a ≠ b ∧ h a = h b := by
  simp only [collidingPairList?, Option.map_eq_some_iff] at hab
  obtain ⟨⟨⟨a', da⟩, ⟨b', db⟩⟩, hfind, ⟨⟩⟩ := hab
  have hmem := List.mem_of_find?_eq_some hfind
  have htest := List.find?_some hfind
  simp only [List.mem_product, List.mem_map, Prod.mk.injEq] at hmem
  obtain ⟨⟨a'', ha'', rfl, rfl⟩, ⟨b'', hb'', rfl, rfl⟩⟩ := hmem
  simp only [decide_eq_true_eq] at htest
  exact ⟨ha'', hb'', htest.2, htest.1⟩

/-- `collidingPairList?` finds a pair exactly when the messages contain a collision. -/
theorem isSome_collidingPairList?_iff {h : α → β} {ms : List α} :
    (collidingPairList? h ms).isSome ↔ ∃ a ∈ ms, ∃ b ∈ ms, a ≠ b ∧ h a = h b := by
  constructor
  · intro hs
    obtain ⟨⟨a, b⟩, hab⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨ha, hb, hne, heq⟩ := collidingPairList?_eq_some hab
    exact ⟨a, ha, b, hb, hne, heq⟩
  · rintro ⟨a, ha, b, hb, hne, heq⟩
    simp only [collidingPairList?, Option.isSome_map, List.find?_isSome]
    exact ⟨((a, h a), (b, h b)), by simp [ha, hb], by simp [heq, hne]⟩

/-- **Brute force** ([BonehShoup2023], §8.3, printed pp. 293–294): among more than `2 ^ ℓ`
distinct messages with `ℓ`-bit digests, two have the same digest. -/
theorem isSome_collidingPairList?_of_two_pow_lt {h : α → List Bool} {ms : List α} {ℓ : ℕ}
    (hlen : ∀ m ∈ ms, (h m).length = ℓ) (hnd : ms.Nodup) (hlt : 2 ^ ℓ < ms.length) :
    (collidingPairList? h ms).isSome := by
  rw [isSome_collidingPairList?_iff]
  have hcard : (BitString.wordsOfLength ℓ).card < ms.toFinset.card := by
    rw [BitString.card_wordsOfLength, List.toFinset_card_of_nodup hnd]; exact hlt
  obtain ⟨a, ha, b, hb, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to (f := h) hcard
    fun m hm => BitString.mem_wordsOfLength.mpr (hlen m (List.mem_toFinset.mp hm))
  exact ⟨a, List.mem_toFinset.mp ha, b, List.mem_toFinset.mp hb, hne, heq⟩

end Search

/-- Searching computed messages for a collision of a keyed polynomial-time hash. -/
theorem computableInPolyTime_collidingPairList? {γ : Type} {encIn : γ ↪ List Bool}
    {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {key : γ → List Bool} {msgs : γ → List (List Bool)}
    (hkey : ComputableInPolyTime key encIn encBits)
    (hmsgs : ComputableInPolyTime msgs encIn (encList encBits)) :
    ComputableInPolyTime (fun x => (collidingPairList? (H (key x)) (msgs x)).getD ([], []))
      encIn (encPair encBits encBits) := by
  have hpair : ComputableInPolyTime (fun p : γ × List Bool => (p.2, H (key p.1) p.2))
      (encPair encIn encBits) (encPair encBits encBits) :=
    (ComputableInPolyTime.snd _ _).prod (hH.comp ((hkey.comp (.fst _ _)).prod (.snd _ _)))
  have hds : ComputableInPolyTime (fun x => (msgs x).map fun m => (m, H (key x) m)) encIn
      (encList (encPair encBits encBits)) :=
    ComputableInPolyTime.mapWithInput (f := fun x m => (m, H (key x) m)) hmsgs hpair
  have hprod : ComputableInPolyTime (fun x =>
      (msgs x).map (fun m => (m, H (key x) m)) ×ˢ (msgs x).map fun m => (m, H (key x) m)) encIn
      (encList (encPair (encPair encBits encBits) (encPair encBits encBits))) := by
    simp only [SProd.sprod, List.product]
    refine ComputableInPolyTime.flatMapWithInput
      (f := fun x a => ((msgs x).map fun m => (m, H (key x) m)).map (Prod.mk a)) hds ?_
    exact ComputableInPolyTime.mapWithInput
      (f := fun (q : γ × (List Bool × List Bool)) (b : List Bool × List Bool) => (q.2, b))
      (hds.comp (.fst _ _))
      (((ComputableInPolyTime.snd encIn (encPair encBits encBits)).comp (.fst _ _)).prod
        (.snd _ _))
  have hfind := ComputableInPolyTime.findWithInput
    (test := fun _ (p : (List Bool × List Bool) × (List Bool × List Bool)) =>
      decide (p.1.2 = p.2.2 ∧ p.1.1 ≠ p.2.1)) hprod (by fun_prop)
  have helim := ComputableInPolyTime.optionElimWithInput hfind
    (ComputableInPolyTime.const ([], [])) (body := fun _ p => (p.1.1, p.2.1)) (by fun_prop)
  have hgetD : ∀ o : Option ((List Bool × List Bool) × (List Bool × List Bool)),
      (o.map fun p => (p.1.1, p.2.1)).getD ([], []) = o.elim ([], []) fun p => (p.1.1, p.2.1) := by
    intro o; cases o <;> rfl
  exact helim.of_enc_eq fun x => congrArg _ (by rw [collidingPairList?]; exact hgetD _)

/-- The birthday attack as a collision finder: at security parameter `n` and key `k`, sample
`count n` uniform `msgLen n`-bit messages and return the first colliding pair, or `([], [])`. -/
noncomputable def birthdayCollisionFinder (H : List Bool → List Bool → List Bool)
    (msgLen count : ℕ → ℕ) : CollisionFinder := fun n k => do
  let ms ← OracleComp.replicate (count n) (BitString.sampleList (msgLen n))
  return (collidingPairList? (H k) ms).getD ([], [])

/-- Brute force as a collision finder: hash the fixed messages `msgs n` and return the first
colliding pair, or `([], [])`. -/
noncomputable def bruteForceCollisionFinder (H : List Bool → List Bool → List Bool)
    (msgs : ℕ → List (List Bool)) : CollisionFinder := fun n k =>
  pure ((collidingPairList? (H k) (msgs n)).getD ([], []))

/-- The birthday finder is PPT for a polynomial-time hash, message length and sample count. -/
theorem isPPT_birthdayCollisionFinder {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {msgLen count : ℕ → ℕ} (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hcount : ComputableInPolyTime count encUnary encUnary) :
    IsPPT (encPair encBits encBits) (birthdayCollisionFinder H msgLen count) := by
  have hsearch := computableInPolyTime_collidingPairList? hH
    (key := fun q : (ℕ × List Bool) × List (List Bool) => q.1.2) (msgs := fun q => q.2)
    ((ComputableInPolyTime.snd encUnary encBits).comp
      (.fst (encPair encUnary encBits) (encList encBits))) (.snd _ _)
  change IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
    (fun p => birthdayCollisionFinder H msgLen count p.1 p.2)
  dsimp only [birthdayCollisionFinder]
  ppt

/-- Brute force is PPT when the hash and the list of messages are polynomial time. -/
theorem isPPT_bruteForceCollisionFinder {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {msgs : ℕ → List (List Bool)} (hmsgs : ComputableInPolyTime msgs encUnary (encList encBits)) :
    IsPPT (encPair encBits encBits) (bruteForceCollisionFinder H msgs) := by
  change IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
    (fun p => bruteForceCollisionFinder H msgs p.1 p.2)
  exact (computableInPolyTime_collidingPairList? hH (.snd _ _) (hmsgs.comp (.fst _ _))).isPPTOn

/-- The book's sample count `⌈2 √N⌉ + 1`, by integer square roots. -/
private def birthdayCount (N : ℕ) : ℕ := Nat.sqrt (4 * N - 1) + 2

private theorem birthdayCount_eq {N : ℕ} (hN : 0 < N) :
    birthdayCount N = ⌈2 * Real.sqrt (N : ℝ)⌉₊ + 1 := by
  have h2 : 2 * Real.sqrt (N : ℝ) = Real.sqrt ((4 * N : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (by norm_num)]
    congr 1
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h2, Real.natCeil_sqrt_eq, birthdayCount]
  simp only [show 4 * N ≠ 0 by omega, ↓reduceIte]

private theorem computableInPolyTime_birthdayCount {N : ℕ → ℕ}
    (hN : ComputableInPolyTime N encUnary encUnary) :
    ComputableInPolyTime (fun n => birthdayCount (N n)) encUnary encUnary := by
  unfold birthdayCount
  have h4 : ComputableInPolyTime (fun n => 4 * N n - 1) encUnary encUnary := by fun_prop
  have hs := ComputableInPolyTime.unary_sqrt.comp h4
  fun_prop

/-- The birthday finder with the book's count `⌈2 √N⌉ + 1`, `N = 2 ^ ℓ(n)`, is PPT when `msgLen(n)`
and `2 ^ ℓ(n)` are computable in unary in polynomial time. -/
theorem isPPT_birthdayCollisionFinder_book {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {ℓ msgLen : ℕ → ℕ} (hN : ComputableInPolyTime (fun n => 2 ^ ℓ n) encUnary encUnary)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary) :
    IsPPT (encPair encBits encBits) (birthdayCollisionFinder H msgLen
      fun n => ⌈2 * Real.sqrt ((2 ^ ℓ n : ℕ) : ℝ)⌉₊ + 1) := by
  have hcount : (fun n => birthdayCount (2 ^ ℓ n)) =
      fun n => ⌈2 * Real.sqrt ((2 ^ ℓ n : ℕ) : ℝ)⌉₊ + 1 :=
    funext fun n => birthdayCount_eq (Nat.two_pow_pos _)
  rw [← hcount]
  exact isPPT_birthdayCollisionFinder hH hmsgLen (computableInPolyTime_birthdayCount hN)

/-- A lower bound on the finder's success under every `n`-bit key bounds the game. -/
private theorem le_collisionGame_apply_true {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {A : CollisionFinder} {n : ℕ} {c : ℝ≥0∞}
    (h : ∀ k : List Bool, k.length = n →
      c ≤ (ProbComp.eval (A n k)).toOuterMeasure {p | isCollision H valid n k p.1 p.2 = true}) :
    c ≤ ProbComp.eval (collisionGame H valid A n) true := by
  simp only [collisionGame, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  refine PMF.le_bind_apply_on_support _ fun k hk => ?_
  have hev := PMF.bind_pure_decide_apply_true (ProbComp.eval (A n k))
    (fun p => isCollision H valid n k p.1 p.2 = true)
  simp only [Bool.decide_eq_true] at hev
  rw [hev]
  exact h k (BitString.length_of_mem_support_uniformList hk)

/-- **Brute force succeeds** ([BonehShoup2023], §8.3, printed pp. 293–294): searching more than
`2 ^ ℓ(n)` distinct valid messages with `ℓ(n)`-bit digests finds a collision with certainty. -/
theorem succProbability_bruteForceCollisionFinder {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {ℓ : ℕ → ℕ} {msgs : ℕ → List (List Bool)}
    (hlen : ∀ k, ∀ m ∈ msgs k.length, (H k m).length = ℓ k.length)
    (hnd : ∀ n, (msgs n).Nodup) (hlt : ∀ n, 2 ^ ℓ n < (msgs n).length)
    (hvalid : ∀ n, ∀ m ∈ msgs n, valid n m = true) (n : ℕ) :
    Game.succProbability
      (ProbComp.eval (collisionGame H valid (bruteForceCollisionFinder H msgs) n)) = 1 := by
  have h1 : (1 : ℝ≥0∞) ≤ ProbComp.eval (collisionGame H valid (bruteForceCollisionFinder H msgs) n)
      true := by
    refine le_collisionGame_apply_true fun k hk => ?_
    subst hk
    obtain ⟨⟨a, b⟩, hab⟩ := Option.isSome_iff_exists.mp
      (isSome_collidingPairList?_of_two_pow_lt (hlen k) (hnd _) (hlt _))
    obtain ⟨ha, hb, hne, heq⟩ := collidingPairList?_eq_some hab
    have hc : isCollision H valid k.length k a b = true := by
      rw [isCollision_eq_true_iff]; exact ⟨hvalid _ _ ha, hvalid _ _ hb, hne, heq⟩
    simp only [bruteForceCollisionFinder, ProbComp.eval_pure, hab, Option.getD_some,
      PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, hc, ite_true, le_refl]
  rw [Game.succProbability, le_antisymm (PMF.coe_le_one _ _) h1, ENNReal.toNNReal_one]

/-- **Lemma 8.2 for the birthday finder** ([BonehShoup2023], §8.3, printed p. 294): with
`⌈2 √N⌉ + 1` uniform `msgLen(n)`-bit messages, `N = 2 ^ ℓ(n)` and `100 N ≤ 2 ^ msgLen(n)`, the
finder outputs a collision with probability at least `1/2` when `valid` accepts every
`msgLen(n)`-bit message. -/
theorem half_le_succProbability_birthdayCollisionFinder {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {ℓ msgLen : ℕ → ℕ}
    (hlen : ∀ k m, m.length = msgLen k.length → (H k m).length = ℓ k.length)
    (hvalid : ∀ n m, m.length = msgLen n → valid n m = true)
    (hM : ∀ n, 100 * 2 ^ ℓ n ≤ 2 ^ msgLen n) (n : ℕ) :
    (1 / 2 : ℝ≥0) ≤ Game.succProbability (ProbComp.eval (collisionGame H valid
      (birthdayCollisionFinder H msgLen fun n => ⌈2 * Real.sqrt ((2 ^ ℓ n : ℕ) : ℝ)⌉₊ + 1) n)) := by
  set s := ⌈2 * Real.sqrt ((2 ^ ℓ n : ℕ) : ℝ)⌉₊ + 1
  set μ := msgLen n
  suffices h : ENNReal.ofReal (1 / 2) ≤ ProbComp.eval (collisionGame H valid
      (birthdayCollisionFinder H msgLen fun n => ⌈2 * Real.sqrt ((2 ^ ℓ n : ℕ) : ℝ)⌉₊ + 1) n)
        true by
    refine le_trans ?_ (ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) h)
    rw [ENNReal.ofReal, ENNReal.toNNReal_coe, Real.toNNReal_div (by norm_num)]; norm_num
  refine le_collisionGame_apply_true fun k hk => ?_
  let F : (Fin s → (Fin μ → Bool)) → List (List Bool) := fun v =>
    List.ofFn fun i => List.ofFn (v i)
  let g : List (List Bool) → List Bool × List Bool := fun ms =>
    (collidingPairList? (H k) ms).getD ([], [])
  have hlaw : ProbComp.eval (birthdayCollisionFinder H msgLen
      (fun n => ⌈2 * Real.sqrt ((2 ^ ℓ n : ℕ) : ℝ)⌉₊ + 1) n k) =
      (PMF.iid (PMF.uniformOfFintype (Fin μ → Bool)) s).map (g ∘ F) := by
    simp only [birthdayCollisionFinder, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_replicate_iid, BitString.eval_sampleList, BitString.uniformList, PMF.iid_map,
      PMF.map_comp]
    change (PMF.map _ _).bind (PMF.pure ∘ g) = _
    rw [PMF.bind_pure_comp, PMF.map_comp]
    rfl
  let f : (Fin μ → Bool) → List Bool := fun x => H k (List.ofFn x)
  have hf : ∀ x, f x ∈ BitString.wordsOfLength (ℓ n) := fun x =>
    BitString.mem_wordsOfLength.mpr (by rw [← hk]; exact hlen k _ (by simp [hk, μ]))
  have hsub : {x : Fin s → (Fin μ → Bool) | ∃ i j, f (x i) = f (x j) ∧ x i ≠ x j} ⊆
      (g ∘ F) ⁻¹' {p | isCollision H valid n k p.1 p.2 = true} := by
    rintro x ⟨i, j, hfij, hne⟩
    have hsome : (collidingPairList? (H k) (F x)).isSome :=
      isSome_collidingPairList?_iff.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, _,
        List.mem_ofFn.mpr ⟨j, rfl⟩, fun h => hne (List.ofFn_injective h), hfij⟩
    obtain ⟨⟨a, b⟩, hab⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨ha, hb, hab', heq⟩ := collidingPairList?_eq_some hab
    have hlenF : ∀ w ∈ F x, w.length = μ := by
      intro w hw
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      exact List.length_ofFn
    simp only [Set.mem_preimage, Function.comp_apply, g, hab, Option.getD_some,
      Set.mem_ofPred_eq, isCollision_eq_true_iff]
    exact ⟨hvalid _ _ (hlenF a ha), hvalid _ _ (hlenF b hb), hab', heq⟩
  rw [hlaw, PMF.toOuterMeasure_map_apply]
  refine ENNReal.ofReal_le_of_le_toReal ?_
  calc (1 / 2 : ℝ)
      ≤ 1 - Real.exp (-(s * (s - 1) / (2 * (BitString.wordsOfLength (ℓ n)).card))) -
          s.choose 2 * (Fintype.card (Fin μ → Bool) : ℝ)⁻¹ := by
        rw [BitString.card_wordsOfLength, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        exact_mod_cast PMF.half_le_one_sub_exp_neg_sub_choose_of_hundred_mul_le
          (Nat.two_pow_pos _) (hM n)
    _ ≤ ((PMF.iid (PMF.uniformOfFintype (Fin μ → Bool)) s).toOuterMeasure
          {x | ∃ i j, f (x i) = f (x j) ∧ x i ≠ x j}).toReal :=
        PMF.one_sub_exp_neg_sub_choose_le_iid_uniformOfFintype_exists_collision f _ hf s
    _ ≤ _ := ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
          (MeasureTheory.measure_mono hsub)

/-- **The birthday attack** ([BonehShoup2023], §8.3, Lemma 8.2): a polynomial-time keyed hash with
`ℓ(n)`-bit digests on `msgLen(n)`-bit messages, `100 * 2 ^ ℓ(n) ≤ 2 ^ msgLen(n)`, is not collision
resistant on a domain `valid` that accepts every `msgLen(n)`-bit message, when `msgLen(n)` and
`2 ^ ℓ(n)` are computable in unary in polynomial time. -/
theorem not_collisionResistantOn_of_birthday {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {ℓ msgLen : ℕ → ℕ}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hN : ComputableInPolyTime (fun n => 2 ^ ℓ n) encUnary encUnary)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hlen : ∀ k m, m.length = msgLen k.length → (H k m).length = ℓ k.length)
    (hvalid : ∀ n m, m.length = msgLen n → valid n m = true)
    (hM : ∀ n, 100 * 2 ^ ℓ n ≤ 2 ^ msgLen n) :
    ¬ CollisionResistantOn H valid :=
  not_collisionResistantOn_of_le_succProbability (c := 1 / 2) (by norm_num) _
    (isPPT_birthdayCollisionFinder_book hH hN hmsgLen)
    (half_le_succProbability_birthdayCollisionFinder hlen hvalid hM)

/-- **Brute force** ([BonehShoup2023], §8.3, printed pp. 293–294): a polynomial-time keyed hash with
`ℓ(n)`-bit digests is not collision resistant when a polynomial-time list of more than `2 ^ ℓ(n)`
distinct valid messages exists. -/
theorem not_collisionResistantOn_of_bruteForce {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {ℓ : ℕ → ℕ} {msgs : ℕ → List (List Bool)}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hmsgs : ComputableInPolyTime msgs encUnary (encList encBits))
    (hlen : ∀ k, ∀ m ∈ msgs k.length, (H k m).length = ℓ k.length)
    (hnd : ∀ n, (msgs n).Nodup) (hlt : ∀ n, 2 ^ ℓ n < (msgs n).length)
    (hvalid : ∀ n, ∀ m ∈ msgs n, valid n m = true) :
    ¬ CollisionResistantOn H valid :=
  not_collisionResistantOn_of_le_succProbability one_ne_zero _
    (isPPT_bruteForceCollisionFinder hH hmsgs)
    fun n => (succProbability_bruteForceCollisionFinder hlen hnd hlt hvalid n).ge

/-- A polynomial-time keyed hash with `ℓ(n)`-bit digests is not collision resistant when
`2 ^ ℓ(n)` is computable in unary in polynomial time: brute force on `2 ^ ℓ(n) + 1` messages. -/
theorem not_collisionResistant_of_two_pow_polyTime {H : List Bool → List Bool → List Bool}
    {ℓ : ℕ → ℕ}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hN : ComputableInPolyTime (fun n => 2 ^ ℓ n) encUnary encUnary)
    (hlen : ∀ k m, (H k m).length = ℓ k.length) :
    ¬ CollisionResistant H := by
  refine not_collisionResistantOn_of_bruteForce (ℓ := ℓ)
    (msgs := fun n => (List.range (2 ^ ℓ n + 1)).map fun i => List.replicate i false)
    hH ?_ (fun k m _ => hlen k m) ?_ ?_ (fun _ _ _ => rfl)
  · fun_prop
  · exact fun n => List.nodup_range.map fun i j h => by simpa using congrArg List.length h
  · simp

end Cslib.Crypto
