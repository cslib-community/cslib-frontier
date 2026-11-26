/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.Size
public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.CoinTape
public import CslibFrontier.Crypto.Computational.Homomorphic.KeyChain.Size
public import CslibFrontier.Crypto.Computational.Homomorphic.KeyChain.CoinTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Probability.BitString.UniformSplit
import CslibFrontier.Probability.PMF.Bind

/-!
# Saved tapes for the zero-link branch

The original zero-link choice generates its remaining keys, encrypts the zero links and calls
the adversary. A depth-zero choice still calls the adversary on the singleton public key.

## Main definitions

* `Cslib.Crypto.Homomorphic.Leveled.zeroLinkChooseCoins`: replay the original zero-link choice.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.eval_zeroLinkAdversary_choose_eq_map_coins`: exact replay
  from supported-input component laws.
* `Cslib.Crypto.Homomorphic.Leveled.length_encPublicKey_support_zeroLink_le`: actual artifact size.
* `Cslib.Crypto.Homomorphic.Leveled.zeroLinkAdversary_choose_state_length_le`: saved-state size.
* `Cslib.Crypto.Homomorphic.Leveled.computableInPolyTime_zeroLinkChooseCoins`: native replay.
-/

public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Probability Turing.MultiTapeTM

/-- Replay independent key blocks, padded zero-link encryption blocks and the final choice.
At depth zero the first two regions are empty; the adversary still receives the singleton key. -/
@[expose] def zeroLinkChooseCoins
    (evaluateKey : ℕ → List Bool → List Bool × List Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (n depth capacity keyCoins encCoins : ℕ) (challengePk tape : List Bool) :
    (Bool × Bool) × List Bool :=
  let rest := (BitString.listRows depth keyCoins (tape.take (depth * keyCoins))).map
    (evaluateKey n)
  let remaining := tape.drop (depth * keyCoins)
  let links := Scheme.encryptKeyLinksCoins evaluateEncrypt n encCoins capacity true
    ((challengePk, (rest.headD ([], [])).2) :: rest)
    (remaining.take (depth * capacity * encCoins))
  evaluateChoose (n, encPublicKey (challengePk :: rest.map Prod.fst, links))
    (remaining.drop (depth * capacity * encCoins))

/-- The zero-link artifact obeys the same serialized-size bound, including the empty chain.
The placeholder first secret takes its width from the first generated key, or is empty. -/
theorem length_encPublicKey_support_zeroLink_le {E : Scheme} {n capacity pkBound ctBound : ℕ}
    {challengePk : List Bool} {rest : List (List Bool × List Bool)}
    (hpk : challengePk.length ≤ pkBound)
    (hkeys : ∀ key ∈ rest, key.1.length ≤ pkBound ∧ key.2.length ≤ capacity)
    (hencrypt : ∀ pk, pk.length ≤ pkBound → ∀ bit ciphertext,
      ciphertext ∈ (ProbComp.eval (E.encrypt n pk bit)).support → ciphertext.length ≤ ctBound)
    {links : List (List (List Bool))}
    (hlinks : links ∈ (ProbComp.eval
      (E.encryptZeroKeyLinks n ((challengePk, (rest.headD ([], [])).2) :: rest))).support) :
    (encPublicKey (challengePk :: rest.map Prod.fst, links)).length ≤
      publicKeyLengthBound rest.length capacity pkBound ctBound := by
  have hhead : (rest.headD ([], [])).2.length ≤ capacity := by
    cases rest with | nil => simp | cons key _ => exact (hkeys key (by simp)).2
  have hlinksInfo := Scheme.length_and_mem_of_mem_support_encryptZeroKeyLinks
    (E := E) (width := capacity) (ctBound := ctBound)
    (List.forall_mem_cons (a := (challengePk, (rest.headD ([], [])).2)).mpr
      ⟨⟨hhead, hencrypt challengePk hpk⟩,
        fun key hkey => ⟨(hkeys key hkey).2, hencrypt _ (hkeys key hkey).1⟩⟩) hlinks
  exact length_encPublicKey_le rest.length capacity pkBound ctBound _ _ (by simp)
    (List.forall_mem_cons.mpr ⟨hpk, List.forall_mem_map.mpr fun key hkey => (hkeys key hkey).1⟩)
    (by simpa using hlinksInfo.1.le) hlinksInfo.2

/-- Exact choice replay using laws only at generated keys and bounded public artifacts.
Padding reserves `capacity` encryptions per link, independently even for repeated keys. -/
theorem eval_zeroLinkAdversary_choose_eq_map_coins (E : Scheme)
    (adversary : Encryption.Adversary) (depth : ℕ → ℕ)
    (evaluateKey : ℕ → List Bool → List Bool × List Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (n capacity pkBound encCoins keyCoins chooseCoins : ℕ) (challengePk : List Bool)
    (hpk : challengePk.length ≤ pkBound)
    (hkey : ProbComp.eval (E.keyGen n) =
      (BitString.uniformList keyCoins).map (evaluateKey n))
    (hkeys : ∀ key ∈ (ProbComp.eval (E.keyGen n)).support,
      key.1.length ≤ pkBound ∧ key.2.length ≤ capacity)
    (hencrypt : ∀ pk, pk.length ≤ pkBound → ∀ message,
      ProbComp.eval (E.encrypt n pk message) =
        (BitString.uniformList encCoins).map (evaluateEncrypt (n, pk, message)) ∧
      ∀ ciphertext ∈ (ProbComp.eval (E.encrypt n pk message)).support,
        ciphertext.length ≤ encCoins)
    (hchoose : ∀ artifact, (encPublicKey artifact).length ≤
        publicKeyLengthBound (depth n) capacity pkBound encCoins →
      ProbComp.eval (adversary.choose n (encPublicKey artifact)) =
        (BitString.uniformList chooseCoins).map
          (evaluateChoose (n, encPublicKey artifact))) :
    ProbComp.eval ((zeroLinkAdversary E depth adversary).choose n challengePk) =
      (BitString.uniformList (depth n * keyCoins +
        (depth n * capacity * encCoins + chooseCoins))).map
        (zeroLinkChooseCoins evaluateKey evaluateEncrypt evaluateChoose n (depth n) capacity
          keyCoins encCoins challengePk) := by
  simp only [zeroLinkAdversary, ProbComp.eval_bind]
  trans (ProbComp.eval (OracleComp.replicate (depth n) (E.keyGen n))).bind (fun rest =>
    (BitString.uniformList (depth n * capacity * encCoins)).bind (fun linkTape =>
      (BitString.uniformList chooseCoins).map (fun chooseTape =>
        evaluateChoose (n, encPublicKey (challengePk :: rest.map Prod.fst,
          Scheme.encryptKeyLinksCoins evaluateEncrypt n encCoins capacity true
            ((challengePk, (rest.headD ([], [])).2) :: rest) linkTape)) chooseTape)))
  · refine PMF.bind_congr_on_support _ _ _ fun rest hrest => ?_
    obtain ⟨hlength, hrestKeys⟩ := (ProbComp.mem_support_replicate_iff _ _ _).mp hrest
    have hhead : (rest.headD ([], [])).2.length ≤ capacity := by
      cases rest with | nil => simp | cons k _ => exact (hkeys k (hrestKeys k (by simp))).2
    have hparticipants : ∀ key ∈ (challengePk, (rest.headD ([], [])).2) :: rest,
        key.1.length ≤ pkBound ∧ key.2.length ≤ capacity :=
      List.forall_mem_cons.mpr ⟨⟨hpk, hhead⟩, fun key hmem => hkeys key (hrestKeys key hmem)⟩
    refine (PMF.bind_congr_on_support _ _ _ fun links hlinks => hchoose _ ?_).trans ?_
    · exact hlength ▸ length_encPublicKey_support_zeroLink_le hpk
        (fun key hmem => hkeys key (hrestKeys key hmem))
        (fun pk hpk bit => (hencrypt pk hpk bit).2) hlinks
    have hlinks := E.eval_encryptKeyLinks_eq_map_coins evaluateEncrypt n encCoins capacity true
      ((challengePk, (rest.headD ([], [])).2) :: rest)
      (fun key hmem => (hparticipants key hmem).2)
      (fun key hmem bit => (hencrypt key.1 (hparticipants key hmem).1 bit).1)
    simp only [List.tail_cons, List.length_zip, List.length_cons, Nat.min_eq_right
      (Nat.le_succ _), hlength, ← Nat.mul_assoc, ↓reduceIte] at hlinks
    rw [hlinks, PMF.bind_map]; rfl
  rw [ProbComp.eval_replicate_of_uniformList (depth n) keyCoins _ _ hkey, PMF.bind_map]
  unfold zeroLinkChooseCoins
  dsimp only [Function.comp_def]
  exact (BitString.uniformList_map_split3 _ _ _ _).symm

/-- The saved state of an actual zero-link choice is bounded by its bounded-artifact choice
envelope. This is a support statement about the original choice, independent of its replay. -/
theorem zeroLinkAdversary_choose_state_length_le (E : Scheme)
    (adversary : Encryption.Adversary) (depth : ℕ → ℕ)
    (n capacity pkBound ctBound chooseBound : ℕ) (challengePk : List Bool)
    (hpk : challengePk.length ≤ pkBound)
    (hkeys : ∀ key ∈ (ProbComp.eval (E.keyGen n)).support,
      key.1.length ≤ pkBound ∧ key.2.length ≤ capacity)
    (hencrypt : ∀ pk, pk.length ≤ pkBound → ∀ bit ciphertext,
      ciphertext ∈ (ProbComp.eval (E.encrypt n pk bit)).support → ciphertext.length ≤ ctBound)
    (hchoose : ∀ artifact, (encPublicKey artifact).length ≤
        publicKeyLengthBound (depth n) capacity pkBound ctBound →
      ∀ choice ∈ (ProbComp.eval (adversary.choose n (encPublicKey artifact))).support,
        choice.2.length ≤ chooseBound)
    {choice : (Bool × Bool) × List Bool}
    (hchoice : choice ∈ (ProbComp.eval
      ((zeroLinkAdversary E depth adversary).choose n challengePk)).support) :
    choice.2.length ≤ chooseBound := by
  simp only [zeroLinkAdversary, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hchoice
  obtain ⟨rest, hrest, links, hlinks, hchoice⟩ := hchoice
  obtain ⟨hlength, hrestKeys⟩ := (ProbComp.mem_support_replicate_iff _ _ _).mp hrest
  exact hchoose _ (hlength ▸ length_encPublicKey_support_zeroLink_le hpk
    (fun key hmem => hkeys key (hrestKeys key hmem)) hencrypt hlinks) choice hchoice

/-- Zero-link replay is native polynomial time in every supplied parameter, key and tape.
It retains the original head-default behavior on an empty generated key list. -/
@[fun_prop] theorem computableInPolyTime_zeroLinkChooseCoins
    {evaluateKey : ℕ → List Bool → List Bool × List Bool}
    {evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool}
    {evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool}
    (hkey : ComputableInPolyTime (fun (n, tape) => evaluateKey n tape)
      (encPair encUnary encBits) (encPair encBits encBits))
    (hencrypt : ComputableInPolyTime (fun (input, tape) => evaluateEncrypt input tape)
      (encPair (encKeyedInput encBool) encBits) encBits)
    (hchoose : ComputableInPolyTime (fun (input, tape) => evaluateChoose input tape)
      encChooseCoinsInput (Encryption.encChoiceOut encBool))
    {α : Type} {input : α ↪ List Bool} {n depth capacity keyCoins encCoins : α → ℕ}
    {challengePk tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hdepth : ComputableInPolyTime depth input encUnary)
    (hcapacity : ComputableInPolyTime capacity input encUnary)
    (hkeyCoins : ComputableInPolyTime keyCoins input encUnary)
    (hencCoins : ComputableInPolyTime encCoins input encUnary)
    (hpk : ComputableInPolyTime challengePk input encBits)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => zeroLinkChooseCoins evaluateKey evaluateEncrypt evaluateChoose
      (n a) (depth a) (capacity a) (keyCoins a) (encCoins a) (challengePk a) (tape a))
      input (Encryption.encChoiceOut encBool) := by
  fun_prop [zeroLinkChooseCoins]

end Cslib.Crypto.Homomorphic.Leveled
