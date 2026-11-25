/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Kolmogorov.TimeBounded
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Complexity.Classes.Ladner.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Tactic.EncLen

/-!
# The Minimum `Kt` Problem (`MKtP`) and `GapMKtP`

This module develops the decision and promise problems associated with Levin's time-bounded
Kolmogorov complexity `Cslib.Kolmogorov.levinKt` ($\mathrm{Kt}$):

* **Exponential-step witness characterization (`levinKt_le_natCast_iff_exists_runFor_two_pow`):**
  $\mathrm{Kt}(x) \le k$ if and only if some binary program $p$ of length at most $k$ outputs $x$
  within $2^{k - |p|}$ steps under `universalTM`.
* **Optimal `Kt`-witnesses and running-time bound for random strings
  (`exists_length_add_clog_eq_levinKtNat`, `encard_setOf_forall_optimal_levinKt_two_pow_lt`,
  `two_pow_lt_ncard_setOf_exists_optimal_levinKt_le_two_pow`):**
  Every string $x$ admits an optimal $\mathrm{Kt}$-witness $(p, s)$ with $s > 0$ and
  $|p| + \lceil \log_2 s \rceil = \mathrm{Kt}(x)$. Following
  [Liu and Pass, Section 3.1, Fact 3.1, p. 10][LiuPass2021Crypto], if any witness $(p, s)$
  satisfying $|p| + \lceil \log_2 s \rceil \le \mathrm{Kt}(x)$ runs for more than
  $2^{\mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil + m}$ steps, then $K(x) < |x| - m$;
  consequently, all but fewer than $2^{n - m}$ strings of length $n$ have an optimal
  $\mathrm{Kt}$-witness running in at most
  $2^{\mathrm{copyOverhead} + \lceil \log_2(n + 1) \rceil + m}$ steps. Here the extra
  $\lceil \log_2(n + 1) \rceil$ term in the exponent (relative to Liu–Pass's $2^c / \varepsilon$
  bound from Fact 2.1, $\mathrm{Kt}(x) \le |x| + c$) comes from our multi-tape bound
  `levinKt_le_length_add`
  ($\mathrm{Kt}(x) \le |x| + \mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil$).
* **`MKtP ∈ E ⊆ EXP` (`MKtP.mem_E`, `MKtP.mem_EXP`, `MKtPAt.mem_EXP`):**
  `Cslib.Kolmogorov.MKtP` is the set of instances `i : MKtPInstance` with
  `levinKt i.word ≤ i.threshold`, and `Cslib.Kolmogorov.MKtPAt s` is the fixed-threshold language
  `{x | levinKt x ≤ s x.length}`
  ([Liu and Pass, Section 2.2][LiuPass2021Crypto];
  [Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]; compare
  `R_Kt ∈ E` in
  [Allender et al., Definitions 1 and 6][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]).
  While [Liu and Pass, Section 2.2][LiuPass2021Crypto] encode the threshold $k$ in binary as a
  $\lceil \log_2 n \rceil$-bit integer (in their model Fact 2.1 gives $\mathrm{Kt}(x) \le |x| + c$,
  and in ours `levinKt_le_length_add` gives
  $\mathrm{Kt}(x) \le |x| + \mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil$), here `MKtP` is
  paired with the unary threshold encoding `encMKtP` (`encPair encBits encUnary` on
  `(i.word, i.threshold)`) so that `i.threshold + 1 ≤ (encMKtP i).length` holds unconditionally for
  arbitrary `i.threshold ∈ ℕ` without a syntactic $k < 2 |x|$ side condition; for nontrivial
  thresholds $k \le O(|x|)$ and for every polynomial-time unary threshold $s$ in `MKtPAt s`, the
  unary encoding has polynomial length and `EXP` membership transfers via
  `PolyTimeReducible.mem_EXP`.
  Enumerating candidate programs `Ladner.word j` of length at most `i.threshold` and running
  `universalTMRunFor` for $2^{\mathtt{i.threshold} - |p|}$ steps places `MKtP` in `E encMKtP` and
  `EXP encMKtP`, and places `MKtPAt s` in `EXP encBits` whenever `s` is computable in polynomial
  time in unary.
* **Promise problem `GapMKtP` (`Cslib.Kolmogorov.GapMKtP`):**
  The promise problem separating $\mathrm{Kt}(x) \le s_1(|x|)$ from $\mathrm{Kt}(x) > s_2(|x|)$
  for $s_1 \le s_2$
  ([Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]).

## Main definitions

* `Cslib.Kolmogorov.MKtPInstance`, `Cslib.Kolmogorov.encMKtP`, `Cslib.Kolmogorov.MKtP`: instances,
  unary-threshold encoding, and yes-set of the Minimum `Kt` Problem.
* `Cslib.Kolmogorov.MKtP.boundedSearch`: polynomial-time bounded search for a `Kt`-witness up to
  word-index and step cap `N`.
* `Cslib.Kolmogorov.MKtPAt`: the fixed-threshold language $\{x \mid \mathrm{Kt}(x) \le s(|x|)\}$.
* `Cslib.Kolmogorov.GapMKtP`, `Cslib.Kolmogorov.GapMKtP.yesSet`,
  `Cslib.Kolmogorov.GapMKtP.noSet`: the promise problem `GapMKtP[s₁, s₂]`.

## Main results

* `Cslib.Kolmogorov.levinKt_le_natCast_iff_exists_runFor_two_pow`,
  `Cslib.Kolmogorov.levinKtNat_le_iff_exists_runFor_two_pow`: exponential-step witness
  characterization of $\mathrm{Kt}(x) \le k$.
* `Cslib.Kolmogorov.exists_length_add_clog_eq_levinKt`,
  `Cslib.Kolmogorov.exists_length_add_clog_eq_levinKtNat`: existence of an optimal `Kt`-witness.
* `Cslib.Kolmogorov.plain_lt_of_levinKtNat_witness_two_pow_lt`,
  `Cslib.Kolmogorov.encard_setOf_forall_optimal_levinKt_two_pow_lt`,
  `Cslib.Kolmogorov.two_pow_lt_ncard_setOf_exists_optimal_levinKt_le_two_pow`:
  running-time bound for optimal `Kt`-witnesses ([Liu and Pass, Section 3.1,
  Fact 3.1, p. 10][LiuPass2021Crypto]).
* `Cslib.Kolmogorov.MKtP.computableInPolyTime_boundedSearch`,
  `Cslib.Kolmogorov.MKtP.boundedSearch_eq_true_iff_of_two_pow_le`: polynomial-time certificate and
  exactness of `MKtP.boundedSearch`.
* `Cslib.Kolmogorov.MKtP.mem_E`, `Cslib.Kolmogorov.MKtP.mem_EXP`: `MKtP` is in `E encMKtP` and
  `EXP encMKtP`.
* `Cslib.Kolmogorov.MKtPAt.polyTimeReducible_MKtP`, `Cslib.Kolmogorov.MKtPAt.mem_EXP`,
  `Cslib.Kolmogorov.MKtPAt.mem_EXP_polynomial`: `MKtPAt s ∈ EXP encBits` for polynomial-time unary
  thresholds `s`.
* `Cslib.Kolmogorov.GapMKtP.disjoint_yesSet_noSet`, `Cslib.Kolmogorov.GapMKtP.id_eq`: consistency
  and zero-gap specialization of `GapMKtP`.

## References

* [E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek, D. Ronneburger,
  *Power from Random Strings*][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]
* [L. A. Levin, *Universal Sequential Search Problems*][Levin1973]
* [L. A. Levin, *Randomness Conservation Inequalities; Information and Independence in
  Mathematical Theories*][Levin1984]
* [Y. Liu, R. Pass, *On the Possibility of Basing Cryptography on EXP ≠ BPP*][LiuPass2021Crypto]
* [I. C. Oliveira, R. Santhanam, *Hardness Magnification for Natural
  Problems*][OliveiraSanthanam2018]
-/

public section

namespace Cslib.Kolmogorov

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal
open Cslib.Complexity DescriptionMethod

/-! ### Exponential-step witness characterization and optimal witnesses for `levinKt` -/

/-- **Exponential-step characterization of `levinKt`.** $\mathrm{Kt}(x) \le k$ iff some binary
program $p$ of length at most $k$ outputs $x$ within $2^{k - |p|}$ steps under `universalTM`. -/
theorem levinKt_le_natCast_iff_exists_runFor_two_pow {x : List Bool} {k : ℕ} :
    levinKt x ≤ k ↔
      ∃ p : List Bool, p.length ≤ k ∧ x ∈ (universalTM.run p).runFor (2 ^ (k - p.length)) :=
  levinKt_le_natCast_iff.trans exists_runFor_length_add_clog_le_iff

/-- `ℕ`-valued exponential-step characterization of `levinKtNat`. -/
theorem levinKtNat_le_iff_exists_runFor_two_pow {x : List Bool} {k : ℕ} :
    levinKtNat x ≤ k ↔
      ∃ p : List Bool, p.length ≤ k ∧ x ∈ (universalTM.run p).runFor (2 ^ (k - p.length)) :=
  levinKtNat_le_iff.trans levinKt_le_natCast_iff_exists_runFor_two_pow

/-- Every string `x` admits an optimal `Kt`-witness `(p, s)` with `0 < s`,
`x ∈ (universalTM.run p).runFor s`, and `p.length + Nat.clog 2 s = levinKtNat x`. -/
theorem exists_length_add_clog_eq_levinKtNat (x : List Bool) :
    ∃ (p : List Bool) (s : ℕ),
      0 < s ∧ x ∈ (universalTM.run p).runFor s ∧ p.length + Nat.clog 2 s = levinKtNat x := by
  obtain ⟨p, s, hp, hle⟩ := levinKt_le_natCast_iff.mp (natCast_levinKtNat x).symm.le
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [universalTM_runFor, universalTMRunFor_zero] at hp
  refine ⟨p, s, hs, hp, le_antisymm hle (levinKtNat_le_iff.mpr ?_)⟩
  refine (levinKt_le_timeBoundedAt_add s x).trans ?_
  rw [Nat.cast_add]
  exact add_le_add_left (etimeBoundedComplexity_le_length hp) _

/-- Every string `x` admits an optimal `Kt`-witness `(p, s)` in `ℕ∞` with `0 < s`,
`x ∈ (universalTM.run p).runFor s`, and `(p.length + Nat.clog 2 s : ℕ) = levinKt x`. -/
theorem exists_length_add_clog_eq_levinKt (x : List Bool) :
    ∃ (p : List Bool) (s : ℕ),
      0 < s ∧ x ∈ (universalTM.run p).runFor s ∧
        ((p.length + Nat.clog 2 s : ℕ) : ℕ∞) = levinKt x := by
  obtain ⟨p, s, hs, hp, heq⟩ := exists_length_add_clog_eq_levinKtNat x
  exact ⟨p, s, hs, hp, by rw [heq, natCast_levinKtNat]⟩

/-- **[Liu and Pass, Section 3.1, Fact 3.1, p. 10][LiuPass2021Crypto]:**
If $(p, s)$ outputs $x$ within $s$ steps with $|p| + \lceil \log_2 s \rceil \le \mathrm{Kt}(x)$, and
$s > 2^{\mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil + m}$ (with $m \le |x|$), then the
plain Kolmogorov complexity of $x$ satisfies $K(x) < |x| - m$. The extra
$\lceil \log_2(|x| + 1) \rceil$ term in the exponent (relative to Liu–Pass's $2^c / \varepsilon$
from Fact 2.1, $\mathrm{Kt}(x) \le |x| + c$) comes from `levinKt_le_length_add`
($\mathrm{Kt}(x) \le |x| + \mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil$). -/
theorem plain_lt_of_levinKtNat_witness_two_pow_lt {x p : List Bool} {s m : ℕ}
    (hm : m ≤ x.length)
    (hp : x ∈ (universalTM.run p).runFor s)
    (hopt : p.length + Nat.clog 2 s ≤ levinKtNat x)
    (hs : 2 ^ (copyOverhead + Nat.clog 2 (x.length + 1) + m) < s) :
    plain x < (x.length - m : ℕ) := by
  have := levinKtNat_le_iff.mpr (levinKt_le_length_add x)
  have := (Nat.lt_clog_iff_pow_lt one_lt_two).mpr hs
  exact (ecomplexity_le_length (.of_mem_runFor hp)).trans_lt
    (by exact_mod_cast (by omega : p.length < x.length - m))

/-- **[Liu and Pass, Section 3.1, Fact 3.1, p. 10][LiuPass2021Crypto]:**
For $m \le n$, fewer than $2^{n - m}$ strings $x \in \{0, 1\}^n$ have the property that every
optimal $\mathrm{Kt}$-witness $(p, s)$ for $x$ runs for more than
$2^{\mathrm{copyOverhead} + \lceil \log_2(n + 1) \rceil + m}$ steps (with the extra
$\lceil \log_2(n + 1) \rceil$ term coming from `levinKt_le_length_add`). -/
theorem encard_setOf_forall_optimal_levinKt_two_pow_lt {n m : ℕ} (hm : m ≤ n) :
    {x : List Bool | x.length = n ∧
      ∀ (p : List Bool) (s : ℕ),
        x ∈ (universalTM.run p).runFor s →
          p.length + Nat.clog 2 s ≤ levinKtNat x →
            2 ^ (copyOverhead + Nat.clog 2 (n + 1) + m) < s}.encard < 2 ^ (n - m) := by
  refine (Set.encard_le_encard ?_).trans_lt
    (universalTM.encard_setOf_ecomplexity_lt (n - m))
  rintro x ⟨rfl, hall⟩
  obtain ⟨p, s, _, hp, hopt⟩ := exists_length_add_clog_eq_levinKtNat x
  exact plain_lt_of_levinKtNat_witness_two_pow_lt hm hp hopt.le (hall p s hp hopt.le)

/-- **[Liu and Pass, Section 3.1, Fact 3.1, p. 10][LiuPass2021Crypto]:**
For $m \le n$, all but fewer than $2^{n - m}$ of the $2^n$ strings of length $n$ admit an optimal
$\mathrm{Kt}$-witness $(p, s)$ running in at most
$2^{\mathrm{copyOverhead} + \lceil \log_2(n + 1) \rceil + m}$ steps (with the extra
$\lceil \log_2(n + 1) \rceil$ term coming from `levinKt_le_length_add`). -/
theorem two_pow_lt_ncard_setOf_exists_optimal_levinKt_le_two_pow {n m : ℕ} (hm : m ≤ n) :
    2 ^ n <
      {x : List Bool | x.length = n ∧
        ∃ (p : List Bool) (s : ℕ),
          x ∈ (universalTM.run p).runFor s ∧
            p.length + Nat.clog 2 s ≤ levinKtNat x ∧
              s ≤ 2 ^ (copyOverhead + Nat.clog 2 (n + 1) + m)}.ncard + 2 ^ (n - m) := by
  have hfin : {x : List Bool | x.length = n ∧
      ∃ (p : List Bool) (s : ℕ),
        x ∈ (universalTM.run p).runFor s ∧
          p.length + Nat.clog 2 s ≤ levinKtNat x ∧
            s ≤ 2 ^ (copyOverhead + Nat.clog 2 (n + 1) + m)}.Finite :=
    (Set.finite_of_encard_eq_coe (BitString.encard_setOf_length_eq n)).subset fun _ hx => hx.1
  refine (universalTM.two_pow_lt_ncard_setOf_length_eq_le_ecomplexity_add n m).trans_le
    (Nat.add_le_add_right (Set.ncard_le_ncard ?_ hfin) _)
  rintro x ⟨rfl, hplain⟩
  obtain ⟨p, s, _, hp, hopt⟩ := exists_length_add_clog_eq_levinKtNat x
  refine ⟨rfl, p, s, hp, hopt.le, le_of_not_gt fun hlt => ?_⟩
  exact not_lt_of_ge hplain (plain_lt_of_levinKtNat_witness_two_pow_lt hm hp hopt.le hlt)

/-! ### The Minimum `Kt` Problem (`MKtP`) and `MKtP ∈ E ⊆ EXP` -/

/-- An instance of the Minimum `Kt` Problem (`MKtP`)
([Liu and Pass, Section 2.2][LiuPass2021Crypto];
[Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]): a target binary
string `word` paired with an upper-bound threshold `threshold` on Levin's time-bounded Kolmogorov
complexity `levinKt word`. -/
@[ext]
structure MKtPInstance where
  /-- The target binary string `x` whose Levin `Kt` complexity is bounded. -/
  word : List Bool
  /-- The upper-bound threshold `k` on `levinKt word` (encoded in unary by `encMKtP`). -/
  threshold : ℕ
  deriving DecidableEq

/-- Unary-threshold encoding of `MKtPInstance`: frames `word : List Bool` (`encBits`) followed by
`1^threshold` in unary (`encUnary`), with the exact encoded words of
`encPair encBits encUnary (i.word, i.threshold)`. -/
enc_structure encMKtP : MKtPInstance where
  word : encBits, threshold : encUnary

/-- **The Minimum `Kt` Problem (`MKtP`)**
([Liu and Pass, Section 2.2][LiuPass2021Crypto];
[Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]): the set of
instances `i : MKtPInstance` such that `levinKt i.word ≤ i.threshold`. In the complexity-class
statements below (`MKtP.mem_E`, `MKtP.mem_EXP`), `MKtP` is encoded by `encMKtP` (with `i.threshold`
in unary rather than the $\lceil \log_2 n \rceil$-bit binary representation of
[Liu and Pass, Section 2.2][LiuPass2021Crypto]) so that `i.threshold + 1 ≤ (encMKtP i).length`
holds for all `i.threshold ∈ ℕ` without a side condition bounding `i.threshold`. -/
def MKtP : Set MKtPInstance :=
  {i | levinKt i.word ≤ i.threshold}

namespace MKtP

/-- An instance `i` belongs to `MKtP` iff `levinKt i.word ≤ i.threshold`. -/
theorem mem_iff {i : MKtPInstance} : i ∈ MKtP ↔ levinKt i.word ≤ i.threshold :=
  Iff.rfl

/-- `⟨x, k⟩ ∈ MKtP` iff `levinKt x ≤ k`. -/
@[simp]
theorem mk_mem_iff {x : List Bool} {k : ℕ} :
    (⟨x, k⟩ : MKtPInstance) ∈ MKtP ↔ levinKt x ≤ k :=
  Iff.rfl

/-- An instance `i` belongs to `MKtP` iff `levinKtNat i.word ≤ i.threshold`. -/
theorem mem_iff_levinKtNat_le {i : MKtPInstance} :
    i ∈ MKtP ↔ levinKtNat i.word ≤ i.threshold :=
  levinKtNat_le_iff.symm

/-- An instance `i` belongs to `MKtP` iff some program `p` of length at most `i.threshold` outputs
`i.word` within `2 ^ (i.threshold - |p|)` steps under `universalTM`. -/
theorem mem_iff_exists_runFor_two_pow {i : MKtPInstance} :
    i ∈ MKtP ↔
      ∃ p : List Bool, p.length ≤ i.threshold ∧
        i.word ∈ (universalTM.run p).runFor (2 ^ (i.threshold - p.length)) :=
  levinKt_le_natCast_iff_exists_runFor_two_pow

/-- Monotonicity of `MKtP` in the threshold `k`. -/
theorem mem_of_le {x : List Bool} {k₁ k₂ : ℕ}
    (h : (⟨x, k₁⟩ : MKtPInstance) ∈ MKtP) (hk : k₁ ≤ k₂) :
    (⟨x, k₂⟩ : MKtPInstance) ∈ MKtP :=
  mk_mem_iff.mpr ((mk_mem_iff.mp h).trans (Nat.cast_le.mpr hk))

/-- Bounded brute-force search for a `Kt`-witness of an `MKtPInstance` `i` up to word-index and
step cap `N`: checks whether some word `p = Ladner.word j` with `j < N` has
`p.length ≤ i.threshold` and outputs `i.word` within `min (2 ^ (i.threshold - p.length)) N`
steps. -/
def boundedSearch (i : MKtPInstance) (N : ℕ) : Bool :=
  (List.range N).any fun j =>
    decide ((Ladner.word j).length ≤ i.threshold) &&
      decide (universalTMRunFor (Ladner.word j)
        (Ladner.capPow 2 (i.threshold - (Ladner.word j).length) N) = some i.word)

/-- Whenever $2^{\mathtt{i.threshold} + 1} \le N$, `boundedSearch i N = true` iff `i ∈ MKtP`. -/
theorem boundedSearch_eq_true_iff_of_two_pow_le {i : MKtPInstance} {N : ℕ}
    (hN : 2 ^ (i.threshold + 1) ≤ N) :
    boundedSearch i N = true ↔ i ∈ MKtP := by
  dsimp only [boundedSearch]
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    mem_iff_exists_runFor_two_pow]
  refine ⟨fun ⟨j, _, h1, h2⟩ => ⟨Ladner.word j, h1,
    universalTM_runFor _ _ ▸ universalTMRunFor_mono _ (Nat.min_le_left _ _) h2⟩, ?_⟩
  rintro ⟨p, hplen, hp⟩
  refine ⟨Ladner.index p, ?_, ?_⟩
  · have := Ladner.index_add_two_le p
    have : 2 ^ (p.length + 1) ≤ 2 ^ (i.threshold + 1) := by gcongr
    omega
  · simpa only [Ladner.word_index, Ladner.capPow, Nat.min_eq_left
      ((Nat.pow_le_pow_right (by norm_num) ((Nat.sub_le _ _).trans (Nat.le_succ _))).trans hN)]
      using ⟨hplen, hp⟩

/-- `boundedSearch` is computable in polynomial time when the instance is encoded by `encMKtP` and
the search cap `N` is encoded in unary. -/
@[fun_prop]
theorem computableInPolyTime_boundedSearch {α : Type} {encIn : α ↪ List Bool}
    {f : α → MKtPInstance} {N : α → ℕ}
    (hf : ComputableInPolyTime f encIn encMKtP)
    (hN : ComputableInPolyTime N encIn encUnary) :
    ComputableInPolyTime (fun a => boundedSearch (f a) (N a)) encIn encBool := by
  -- A `==` comparison of the run is much cheaper for `fun_prop` than a `decide` atom.
  dsimp only [boundedSearch]
  simp only [← beq_eq_decide]
  fun_prop

/-- **`MKtP` is in linear exponential time `E`** with respect to `encMKtP`. -/
theorem mem_E : MKtP ∈ E encMKtP := by
  obtain ⟨C, D, h⟩ := ComputableInPolyTime.exists_computableInO_pad
    (f := fun q : MKtPInstance × ℕ => boundedSearch q.1 q.2)
    (ν := fun i => i.threshold + 1) (by fun_prop) (by fun_prop)
  rw [show MKtP = {i | boundedSearch i (2 ^ (i.threshold + 1)) = true} from
    Set.ext fun _ => (boundedSearch_eq_true_iff_of_two_pow_le le_rfl).symm]
  refine mem_E_iff.mpr ⟨2 * D, DTIME_mono_of_le_mul_add (C := C) (fun _ => le_rfl)
    (setOf_mem_DTIME_of_computableInO (t := fun n => C * 2 ^ (2 * D * n) + C) h fun i => ?_)⟩
  have hn : i.threshold + 1 ≤ (encMKtP i).length := by enc_len [encMKtP_apply]
  calc C * 2 ^ (D * (i.threshold + 1)) * ((encMKtP i).length + 1) ^ D
      ≤ C * 2 ^ (D * (encMKtP i).length) * (2 ^ (encMKtP i).length) ^ D := by
        gcongr
        exact Nat.lt_two_pow_self
    _ = C * 2 ^ (2 * D * (encMKtP i).length) := by ring
    _ ≤ _ := Nat.le_add_right _ _

/-- **`MKtP` is in `EXP`** with respect to `encMKtP`
([Liu and Pass, Section 2.2][LiuPass2021Crypto]; compare `R_Kt ∈ E` in
[Allender et al., Definition 6][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]). -/
theorem mem_EXP : MKtP ∈ EXP encMKtP :=
  E_subset_EXP mem_E

end MKtP

/-! ### Fixed-threshold formulation (`MKtPAt`) -/

/-- **Fixed-threshold `MKtP`** (`MKtPAt s`,
[Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018];
[Liu and Pass, Section 2.2][LiuPass2021Crypto]): the language of binary strings `x` with
`levinKt x ≤ s x.length`. -/
def MKtPAt (s : ℕ → ℕ) : Set (List Bool) :=
  {x : List Bool | levinKt x ≤ s x.length}

/-- `x ∈ MKtPAt s` iff `levinKt x ≤ s x.length`. -/
theorem mem_MKtPAt_iff {s : ℕ → ℕ} {x : List Bool} :
    x ∈ MKtPAt s ↔ levinKt x ≤ s x.length :=
  Iff.rfl

/-- `x ∈ MKtPAt s` iff `⟨x, s x.length⟩ ∈ MKtP`. -/
@[simp]
theorem mem_MKtPAt_iff_mem_MKtP {s : ℕ → ℕ} {x : List Bool} :
    x ∈ MKtPAt s ↔ (⟨x, s x.length⟩ : MKtPInstance) ∈ MKtP :=
  Iff.rfl

/-- `x ∈ MKtPAt s` iff `levinKtNat x ≤ s x.length`. -/
theorem mem_MKtPAt_iff_levinKtNat_le {s : ℕ → ℕ} {x : List Bool} :
    x ∈ MKtPAt s ↔ levinKtNat x ≤ s x.length :=
  levinKtNat_le_iff.symm

namespace MKtPAt

/-- Whenever `s` is computable in polynomial time in unary, `MKtPAt s` is polynomial-time
many-one reducible to `MKtP`. -/
theorem polyTimeReducible_MKtP {s : ℕ → ℕ}
    (hs : ComputableInPolyTime s encUnary encUnary) :
    PolyTimeReducible encBits encMKtP (MKtPAt s) MKtP :=
  ⟨fun x => ⟨x, s x.length⟩, by fun_prop, fun _ => Iff.rfl⟩

/-- **Fixed-threshold `MKtPAt s` is in `EXP`** whenever `s` is computable in polynomial time in
unary. -/
theorem mem_EXP {s : ℕ → ℕ} (hs : ComputableInPolyTime s encUnary encUnary) :
    MKtPAt s ∈ EXP encBits :=
  (polyTimeReducible_MKtP hs).mem_EXP MKtP.mem_EXP

/-- For any polynomial threshold `q : Polynomial ℕ`, `MKtPAt q.eval ∈ EXP encBits`. -/
theorem mem_EXP_polynomial (q : Polynomial ℕ) :
    MKtPAt q.eval ∈ EXP encBits :=
  mem_EXP (ComputableInPolyTime.unary_eval q)

end MKtPAt

/-! ### The promise problem `GapMKtP` -/

namespace GapMKtP

/-- The yes-instances of `GapMKtP[s₁, s₂]`: strings `x` with `levinKt x ≤ s₁ x.length`
([Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]). -/
def yesSet (s₁ : ℕ → ℕ) : Set (List Bool) :=
  MKtPAt s₁

/-- The no-instances of `GapMKtP[s₁, s₂]`: strings `x` with `s₂ x.length < levinKt x`
([Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]). -/
def noSet (s₂ : ℕ → ℕ) : Set (List Bool) :=
  {x : List Bool | (s₂ x.length : ℕ∞) < levinKt x}

/-- `x ∈ GapMKtP.yesSet s₁` iff `x ∈ MKtPAt s₁`. -/
theorem mem_yesSet_iff {s₁ : ℕ → ℕ} {x : List Bool} :
    x ∈ yesSet s₁ ↔ x ∈ MKtPAt s₁ :=
  Iff.rfl

/-- `x ∈ GapMKtP.noSet s₂` iff `(s₂ x.length : ℕ∞) < levinKt x`. -/
theorem mem_noSet_iff {s₂ : ℕ → ℕ} {x : List Bool} :
    x ∈ noSet s₂ ↔ (s₂ x.length : ℕ∞) < levinKt x :=
  Iff.rfl

/-- `x ∈ GapMKtP.noSet s₂` iff `s₂ x.length < levinKtNat x`. -/
theorem mem_noSet_iff_lt_levinKtNat {s₂ : ℕ → ℕ} {x : List Bool} :
    x ∈ noSet s₂ ↔ s₂ x.length < levinKtNat x := by
  rw [mem_noSet_iff, ← natCast_levinKtNat x, ENat.natCast_lt_natCast]

/-- When `s₁ n ≤ s₂ n` for all `n`, `GapMKtP.yesSet s₁` and `GapMKtP.noSet s₂` are disjoint. -/
theorem disjoint_yesSet_noSet {s₁ s₂ : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) :
    Disjoint (yesSet s₁) (noSet s₂) := by
  refine Set.disjoint_left.mpr fun x hyes hno => ?_
  have hle : levinKt x ≤ (s₂ x.length : ℕ∞) :=
    hyes.trans (Nat.cast_le.mpr (hs x.length))
  exact not_lt_of_ge hle hno

/-- When `s₁ = s₂`, `GapMKtP.noSet s` is the complement of `MKtPAt s`. -/
theorem noSet_eq_compl (s : ℕ → ℕ) : noSet s = (MKtPAt s)ᶜ := by
  ext x
  simp only [mem_noSet_iff, Set.mem_compl_iff, mem_MKtPAt_iff, not_le]

end GapMKtP

/-- **The `GapMKtP` promise problem**
([Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]):
separates `MKtPAt s₁` (`levinKt x ≤ s₁ |x|`) from `GapMKtP.noSet s₂` (`levinKt x > s₂ |x|`)
whenever `s₁ n ≤ s₂ n`. -/
def GapMKtP (s₁ s₂ : ℕ → ℕ) (hs : ∀ n, s₁ n ≤ s₂ n) : PromiseProblem (List Bool) where
  yes := GapMKtP.yesSet s₁
  no := GapMKtP.noSet s₂
  disjoint := GapMKtP.disjoint_yesSet_noSet hs

namespace GapMKtP

variable {s₁ s₂ : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n)

/-- The yes-instances of `GapMKtP s₁ s₂ hs` are `MKtPAt s₁`. -/
@[simp]
theorem yes_eq : (GapMKtP s₁ s₂ hs).yes = MKtPAt s₁ := by
  ext
  rfl

/-- The no-instances of `GapMKtP s₁ s₂ hs` are `GapMKtP.noSet s₂`. -/
@[simp]
theorem no_eq : (GapMKtP s₁ s₂ hs).no = noSet s₂ := by
  ext
  rfl

/-- With zero gap (`s₁ = s₂ = s`), `GapMKtP` is the decision problem `MKtPAt s` viewed as a promise
problem (`PromiseProblem.ofSet (MKtPAt s)`). -/
@[simp]
theorem id_eq (s : ℕ → ℕ) :
    GapMKtP s s (fun _ => le_rfl) = PromiseProblem.ofSet (MKtPAt s) := by
  ext x
  · rfl
  · rw [no_eq, noSet_eq_compl]
    rfl

end GapMKtP

end Cslib.Kolmogorov
