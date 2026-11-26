/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GenericGroup.Relabel
public import CslibFrontier.Crypto.Game
import CslibFrontier.Foundations.Data.List.SortedAssoc
import CslibFrontier.Languages.Probabilistic.Oracle.CoinFixing
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.QueryCount.Scale
import CslibFrontier.Languages.Probabilistic.RandomOracle.ImageCollision
import CslibFrontier.Languages.Probabilistic.RandomPermutation
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Probability.LinearCombination
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EmbeddingPerm
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.PMF.UniformSubset
import CslibFrontier.Probability.Product
import Mathlib.Algebra.Field.ZMod

/-!
# Generic-group games with linear inputs

A bound, not stated in the book, for a family of games in the generic group model of
[BonehShoup2023], Section 16.3. The bound of Theorem 16.3 for discrete logarithm
(`Cslib.Crypto.GenericGroup.succProbability_dlogGame_le_choose`) is one instance; a bound for
another game of this form is another.

`linearGame W A` draws a uniform injective labeling `L : ZMod q ↪ S` and a uniform point
`x : ι → ZMod q`, gives the adversary the label `L 1` and the labels `L (x i)`, and runs it
against the group oracle of `L` (`runLabeled`). The adversary outputs a value `o : γ` and an
element `w k` of `S` for each `k : κ`; it wins when every `w k` is a label, of `v k` say, and
`W x o v` holds. Suppose that for every `o` and every family of linear forms
`F k = ∑ i, a k i X i + b k`, the test `W x o (F · (x))` holds for at most an `ε` fraction of the
points `x`. Then, for prime `q`, an adversary that makes at most `T` queries to the group oracle
wins with probability at most `C(3T + |ι| + 1 + |κ|, 2) / q + ε` (`succProbability_linearGame_le`).
As in `Cslib.Crypto.GenericGroup.dlogGame`, the budget is `ProbOracleComp.IsQueryBounded`: at most
`T` labeling and group-operation queries on every path, whatever the adversary's private coins.

This is a query bound in an idealized model: it assumes no computational hardness, says nothing
about any specific group, and applies to adversaries that are otherwise unbounded.

The proof is the proof of [BonehShoup2023], Theorem 16.3 (Games 0–2), with linear forms in the
`|ι|` unknowns `X i` in place of linear polynomials in one unknown. It reduces to labels in
`ZMod q` with a uniform permutation as labeling (`Cslib.Crypto.GenericGroup.relabel`), samples the
permutation lazily, and replaces it by a table on linear forms that is identical until two distinct
forms of the table agree at `x`. The table ends with at most `3T + |ι| + 1 + |κ|` forms: the
generator and the inputs, at most three for each query, and one for each output. Over `ZMod q`
with `q` prime, two distinct linear forms agree at a uniform point with probability at most `1 / q`
(`Cslib.Probability.toOuterMeasure_uniform_linearComb_eq`), which gives the first term; this is the
only use of primality. The forms of the outputs in the table do not depend on `x`, so the
hypothesis on `W` gives the second term.

## Main definitions

* `Cslib.Crypto.GenericGroup.linearGame`: the game with linear inputs and winning test `W`.

## Main results

* `Cslib.Crypto.GenericGroup.succProbability_linearGame_le`: the bound
  `C(3T + |ι| + 1 + |κ|, 2) / q + ε`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 16.3, Theorem 16.3 and its proof, pp. 693–695.
-/

public section

namespace Cslib.Crypto.GenericGroup

open Probability OracleComp RandomOracle
open scoped NNReal ENNReal

variable {q : ℕ} {S : Type}

/-- A generic-group game with linear inputs. The labeling `L` and the point `x : ι → ZMod q` are
uniform; the adversary gets `L 1` and the labels `L (x i)`, queries the group oracle of `L`, and
outputs a value `o : γ` and elements `w k` of `S`. It wins when every `w k` is a label, of `v k`
say, and `W x o v` holds. -/
@[expose] noncomputable def linearGame {ι κ γ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [NeZero q] [Fintype S] [DecidableEq S] [Nonempty (ZMod q ↪ S)]
    (W : (ι → ZMod q) → γ → (κ → ZMod q) → Bool)
    (A : S → (ι → S) → ProbOracleComp (GroupOracleSpec q S) (γ × (κ → S))) : Game := do
  let L ← PMF.uniformOfFintype (ZMod q ↪ S)
  let x ← PMF.uniformOfFintype (ι → ZMod q)
  let out ← runLabeled L (A (L 1) fun i => L (x i))
  return decide (∃ v : κ → ZMod q, (∀ k, L (v k) = out.2 k) ∧ W x out.1 v)

variable {ι κ γ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### Reduction to a uniform permutation as labeling -/

/-- The game with labels in `ZMod q` and a uniform permutation `σ` as labeling. The adversary
outputs elements of `ZMod q`, and wins when `W` holds at their preimages under `σ`. -/
private noncomputable def permLinearGame [NeZero q] (W : (ι → ZMod q) → γ → (κ → ZMod q) → Bool)
    (B : ZMod q → (ι → ZMod q) →
      ProbOracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))) : Game := do
  let σ ← PMF.uniformOfFintype (Equiv.Perm (ZMod q))
  let x ← PMF.uniformOfFintype (ι → ZMod q)
  let out ← runLabeled (σ : ZMod q → ZMod q) (B (σ 1) fun i => σ (x i))
  return W x out.1 fun k => σ.symm (out.2 k)

/-- The adversary `A` on labels in `ZMod q`, through the embedding `j`: each output of `A` is read
as the preimage under `j`, or as `0` when it has none. -/
private noncomputable def relabelOut (j : ZMod q ↪ S)
    (A : S → (ι → S) → ProbOracleComp (GroupOracleSpec q S) (γ × (κ → S))) (g : ZMod q)
    (u : ι → ZMod q) : ProbOracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q)) :=
  (fun out => (out.1, fun k => (Function.partialInv j (out.2 k)).getD 0)) <$>
    relabel j (A (j g) fun i => j (u i))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
private theorem isQueryBounded_relabelOut (j : ZMod q ↪ S)
    {A : S → (ι → S) → ProbOracleComp (GroupOracleSpec q S) (γ × (κ → S))} {T : ℕ}
    (hA : ∀ g u, (A g u).IsQueryBounded T) (g : ZMod q) (u : ι → ZMod q) :
    (relabelOut j A g u).IsQueryBounded T :=
  (OracleComp.isCostBounded_map_iff _ _ _).mpr (isQueryBounded_relabel j (hA _ _))

/-- The game with linear inputs is won at most as often as the game with a uniform permutation as
labeling, averaged over the embedding `j`. An output that is not a label loses in the first game
and is read as the preimage of `0` in the second. -/
private theorem linearGame_le_bind_permLinearGame [NeZero q] [Fintype S] [DecidableEq S]
    [Nonempty (ZMod q ↪ S)] (W : (ι → ZMod q) → γ → (κ → ZMod q) → Bool)
    (A : S → (ι → S) → ProbOracleComp (GroupOracleSpec q S) (γ × (κ → S))) :
    linearGame W A true ≤
      (PMF.uniformOfFintype (ZMod q ↪ S)).bind (fun j => permLinearGame W (relabelOut j A))
        true := by
  unfold linearGame permLinearGame
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.uniformOfFintype_embedding_bind_perm_trans]
  refine PMF.bind_apply_mono_on_support _ _ fun j _ =>
    PMF.bind_apply_mono_on_support _ _ fun σ _ => PMF.bind_apply_mono_on_support _ _ fun x _ => ?_
  have hmap : runLabeled (σ : ZMod q → ZMod q) (relabelOut j A (σ 1) fun i => σ (x i)) =
      (fun out => (out.1, fun k => (Function.partialInv j (out.2 k)).getD 0)) <$>
        runLabeled (σ : ZMod q → ZMod q) (relabel j (A (j (σ 1)) fun i => j (σ (x i)))) :=
    OracleComp.interpret_map _ _ _
  rw [hmap, runLabeled_relabel, PMF.monad_map_eq_map, PMF.bind_map]
  refine PMF.bind_apply_mono_on_support
    (runLabeled (fun β => j (σ β)) (A (j (σ 1)) fun i => j (σ (x i)))) _ fun out _ => ?_
  by_cases h : ∃ v : κ → ZMod q, (∀ k, j (σ (v k)) = out.2 k) ∧ W x out.1 v
  · obtain ⟨v, hv, hW⟩ := h
    have hσ : (fun k => σ.symm ((Function.partialInv j (out.2 k)).getD 0)) = v := by
      funext k
      rw [← hv k, Function.partialInv_left j.injective]
      simp
    calc _ ≤ 1 := PMF.coe_le_one _ _
      _ = _ := by simp [hσ, hW]
  · simp [h]

/-! ### Where primality is used -/

/-- Two distinct linear forms over `ZMod q`, `q` prime, agree at a uniform point with probability
at most `1 / q`. -/
private theorem toOuterMeasure_uniform_linearForm_eq_le [NeZero q] (hq : q.Prime)
    {K K' : (ι → ZMod q) × ZMod q} (h : K ≠ K') :
    (PMF.uniformOfFintype (ι → ZMod q)).toOuterMeasure
      {x | ∑ i, K.1 i * x i + K.2 = ∑ i, K'.1 i * x i + K'.2} ≤ 1 / (q : ℝ≥0∞) := by
  have : Fact q.Prime := ⟨hq⟩
  have hsum (x : ι → ZMod q) :
      ∑ i, x i * (K.1 i - K'.1 i) = ∑ i, K.1 i * x i - ∑ i, K'.1 i * x i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  by_cases ha : K.1 = K'.1
  · have hc : K.2 ≠ K'.2 := fun hc => h (Prod.ext ha hc)
    simp [ha, hc]
  · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp ha
    have hd : (fun i => K.1 i - K'.1 i) i₀ ≠ 0 := sub_ne_zero.mpr hi₀
    have key := ZMod.card q ▸ Cslib.Probability.toOuterMeasure_uniform_linearComb_eq (F := ZMod q)
      (d := fun i => K.1 i - K'.1 i) (i₀ := i₀) hd (K'.2 - K.2)
    refine le_of_eq_of_le (congrArg _ (Set.ext fun x => ?_)) key.le
    simp only [Set.mem_ofPred_eq, hsum]
    constructor <;> intro hx <;> linear_combination hx

/-! ### Tabulating queries -/

/-- Run `act k` for each `k` of the list, in order, and return the table of results, which is `0`
off the list. -/
private def tabulateM {I K R : Type} {spec : OracleSpec I} [DecidableEq K] [Zero R]
    (act : K → OracleComp spec R) : List K → OracleComp spec (K → R)
  | [] => pure 0
  | k :: l => do
    let r ← act k
    let t ← tabulateM act l
    return Function.update t k r

private theorem isQueryBounded_tabulateM {I K R : Type} {spec : OracleSpec I} [DecidableEq K]
    [Zero R] {act : K → OracleComp spec R} (hact : ∀ k, (act k).IsQueryBounded 1) (l : List K) :
    (tabulateM act l).IsQueryBounded l.length := by
  induction l with
  | nil => exact IsCostBounded.pure _ 0
  | cons k l ih =>
    exact ((hact k).bind fun r => ih.bind fun t =>
      IsCostBounded.pure (Function.update t k r) 0).mono (by simp only [List.length_cons]; omega)

/-- Against deterministic answers, tabulation returns the table of answers on the list. -/
private theorem interpret_tabulateM_pure {I K R : Type} {spec : OracleSpec I} [DecidableEq K]
    [Zero R] (h : (i : I) → PMF (spec i)) (act : K → OracleComp spec R) (g : K → R)
    (hact : ∀ k, OracleComp.interpret h (act k) = PMF.pure (g k)) (l : List K) :
    OracleComp.interpret h (tabulateM act l) = PMF.pure fun k => if k ∈ l then g k else 0 := by
  induction l with
  | nil => simp only [tabulateM, OracleComp.interpret_pure, List.not_mem_nil, ite_false]; rfl
  | cons k l ih =>
    simp only [tabulateM, interp_norm, pmf_norm, hact, ih]
    congr 1 with k' : 1
    by_cases hk : k' = k <;> simp [hk]

/-- One step of a sequential composition, read through `ψ` and `r`, is a step of another, when the
first stages correspond through `φ` and `r` and every continuation from a state satisfying `I`
does. -/
private theorem map_bind_eq_of_step {A A' B B' σ σ' : Type} (φ : A → A') (ψ : B → B')
    (r : σ → σ') (I : σ → Prop) {m : PMF (A × σ)} {m' : PMF (A' × σ')}
    (hm : m.map (fun x => (φ x.1, r x.2)) = m') (hI : ∀ x ∈ m.support, I x.2)
    (f : A × σ → PMF (B × σ)) (f' : A' × σ' → PMF (B' × σ'))
    (hf : ∀ a s, I s → (f (a, s)).map (fun x => (ψ x.1, r x.2)) = f' (φ a, r s)) :
    (m.bind f).map (fun x => (ψ x.1, r x.2)) = m'.bind f' := by
  rw [PMF.map_bind, ← hm, PMF.bind_map]
  exact PMF.bind_congr_on_support _ _ _ fun x hx => hf x.1 x.2 (hI x hx)

/-- Tabulation under a stateful handler, read through `φ` entrywise and `r` on states, is
tabulation under another handler, when each entry is. -/
private theorem map_run_tabulateM {I I' K R R' Q Q' : Type} {spec : OracleSpec I}
    {spec' : OracleSpec I'} [DecidableEq K] [Zero R] [Zero R']
    (h : (i : I) → StateT Q PMF (spec i)) (h' : (i : I') → StateT Q' PMF (spec' i))
    (act : K → OracleComp spec R) (act' : K → OracleComp spec' R') (φ : R → R') (hφ : φ 0 = 0)
    (r : Q → Q') (I : Q → Prop)
    (hpres : ∀ i s, I s → ∀ a s', (a, s') ∈ (h i s).support → I s')
    (hstep : ∀ k s, I s → ((OracleComp.interpret h (act k)).run s).map
      (fun x => (φ x.1, r x.2)) = (OracleComp.interpret h' (act' k)).run (r s))
    (l : List K) (s : Q) (hs : I s) :
    ((OracleComp.interpret h (tabulateM act l)).run s).map (fun x => (fun k => φ (x.1 k), r x.2)) =
      (OracleComp.interpret h' (tabulateM act' l)).run (r s) := by
  induction l generalizing s with
  | nil => simp [tabulateM, interp_norm, pmf_norm, Pi.zero_def, hφ]
  | cons k l ih =>
    simp only [tabulateM, interp_norm, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure]
    refine map_bind_eq_of_step φ (fun (t : K → R) k => φ (t k)) r I (hstep k s hs)
      (fun x hx => OracleComp.run_interpret_invariant h I hpres (act k) s hs x.1 x.2 hx) _ _ ?_
    intro a s₁ hs₁
    refine map_bind_eq_of_step (fun (t : K → R) k => φ (t k)) (fun (t : K → R) k => φ (t k)) r I
      (ih s₁ hs₁)
      (fun x hx => OracleComp.run_interpret_invariant h I hpres _ s₁ hs₁ x.1 x.2 hx) _ _ ?_
    intro t s₂ _
    simp only [PMF.pure_map]
    congr 2 with k'
    by_cases hk : k' = k <;> simp [hk]

/-! ### Keyed tables

The core bound follows the book's Games 1 and 2. A *key* `(a, b) : (ι → ZMod q) × ZMod q` stands
for the linear form `∑ i, a i X i + b`, and a table records (key, label) pairs. Two primitive
queries act on a table: `fwd K` asks for the label of the key `K`, and `inv ℓ` for the key of the
label `ℓ`; a group query is at most three of them (`toPrim`). The *real* handler (`realStep`)
answers as a lazily sampled permutation of values at `x`. The *symbolic* handler (`symStep`) gives
fresh labels to fresh keys and new constants to unknown labels; it looks at `x` only to raise a
flag when two distinct keys agree at `x`. The two handlers agree until the flag is raised. -/

/-- The value of the linear form `K = (a, b)`, that is `∑ i, a i X i + b`, at `x`. -/
private def ev (x : ι → ZMod q) (K : (ι → ZMod q) × ZMod q) : ZMod q := ∑ i, K.1 i * x i + K.2

omit [DecidableEq ι] in
private theorem ev_zero_left (x : ι → ZMod q) (b : ZMod q) : ev x (0, b) = b := by
  simp [ev]

/-- A table of (key, label) pairs. -/
private abbrev Tab (ι : Type) (q : ℕ) := List (((ι → ZMod q) × ZMod q) × ZMod q)

/-- The primitive queries on a table: the label of a key, and the key of a label. -/
private inductive Prim (ι : Type) (q : ℕ) where
  | fwd (K : (ι → ZMod q) × ZMod q)
  | inv (ℓ : ZMod q)

/-- The reply types of the primitive queries. -/
private abbrev PrimSpec (ι : Type) (q : ℕ) : OracleSpec (Prim ι q)
  | .fwd _ => ZMod q
  | .inv _ => (ι → ZMod q) × ZMod q

/-- The cache of a lazily sampled permutation that the table stands for at `x`. -/
private def rep (x : ι → ZMod q) (tab : Tab ι q) : RandomPermutation.Cache (ZMod q) :=
  tab.map fun e => (ev x e.1, e.2)

omit [DecidableEq ι] in
private theorem rep_cons (x : ι → ZMod q) (e : ((ι → ZMod q) × ZMod q) × ZMod q) (tab : Tab ι q) :
    rep x (e :: tab) = (ev x e.1, e.2) :: rep x tab :=
  rfl

/-- The key of the label `ℓ` in the table. -/
private def keyOf (tab : Tab ι q) (ℓ : ZMod q) : Option ((ι → ZMod q) × ZMod q) :=
  (tab.map Prod.swap).lookup ℓ

/-- Some key of the table other than `K` agrees with `K` at `x`. -/
private def Clash (x : ι → ZMod q) (tab : Tab ι q) (K : (ι → ZMod q) × ZMod q) : Prop :=
  ∃ e ∈ tab, e.1 ≠ K ∧ ev x e.1 = ev x K

private instance (x : ι → ZMod q) (tab : Tab ι q) (K : (ι → ZMod q) × ZMod q) :
    Decidable (Clash x tab K) := by
  unfold Clash; infer_instance

/-- A table whose values at `x` are distinct and whose labels are distinct: a partial bijection
between values and labels. -/
private def Consistent (x : ι → ZMod q) (tab : Tab ι q) : Prop :=
  (tab.map fun e => ev x e.1).Nodup ∧ (tab.map Prod.snd).Nodup

private theorem lookup_eq_none_iff' {β δ : Type} [BEq β] [LawfulBEq β] {l : List (β × δ)}
    {k : β} : l.lookup k = none ↔ ∀ e ∈ l, e.1 ≠ k := by
  simp only [List.lookup_eq_none_iff, bne_iff_ne, ne_comm]

omit [Fintype ι] [DecidableEq ι] in
private theorem keyOf_eq_none_iff {tab : Tab ι q} {ℓ : ZMod q} :
    keyOf tab ℓ = none ↔ ℓ ∉ tab.map Prod.snd := by
  simp only [keyOf, lookup_eq_none_iff', List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Prod.fst_swap, not_exists, not_and]

omit [DecidableEq ι] in
private theorem invLookup_rep (x : ι → ZMod q) (tab : Tab ι q) (ℓ : ZMod q) :
    RandomPermutation.invLookup (rep x tab) ℓ = (keyOf tab ℓ).map (ev x) := by
  unfold RandomPermutation.invLookup rep keyOf
  induction tab with
  | nil => rfl
  | cons e tab ih =>
    obtain ⟨K, m⟩ := e
    simp only [List.map_cons, Prod.swap_prod_mk, List.lookup_cons]
    cases h : (ℓ == m) with
    | true => rfl
    | false => exact ih

omit [DecidableEq ι] in
/-- In a table with distinct values at `x`, the value of a key finds the key's own label. -/
private theorem lookup_rep_of_lookup {x : ι → ZMod q} {tab : Tab ι q}
    (hval : (tab.map fun e => ev x e.1).Nodup) {K : (ι → ZMod q) × ZMod q} {ℓ : ZMod q}
    (h : tab.lookup K = some ℓ) : (rep x tab).lookup (ev x K) = some ℓ := by
  induction tab with
  | nil => simp at h
  | cons e tab ih =>
    obtain ⟨K', m⟩ := e
    rw [List.map_cons, List.nodup_cons] at hval
    simp only [rep, List.map_cons, List.lookup_cons] at h ⊢
    rcases eq_or_ne K K' with rfl | hK
    · simpa using h
    · rw [beq_false_of_ne hK] at h
      have hne : ev x K ≠ ev x K' := fun heq =>
        hval.1 (heq ▸ List.mem_map.mpr ⟨(K, ℓ), List.mem_of_lookup_eq_some h, rfl⟩)
      simpa only [rep, beq_false_of_ne hne] using ih hval.2 h

section Tables

variable [NeZero q]

/-- The labels not in the table. -/
private def freshLabels (tab : Tab ι q) : Finset (ZMod q) :=
  Finset.univ.filter fun ℓ => ℓ ∉ tab.map Prod.snd

/-- The constants `b` such that the constant form `(0, b)` is not a key of the table. -/
private def freshConsts (tab : Tab ι q) : Finset (ZMod q) :=
  Finset.univ.filter fun b => ((0 : ι → ZMod q), b) ∉ tab.map Prod.fst

/-- The values that no key of the table takes at `x`. -/
private def freshValues (x : ι → ZMod q) (tab : Tab ι q) : Finset (ZMod q) :=
  Finset.univ.filter fun y => y ∉ tab.map fun e => ev x e.1

/-- A uniform element of `s`, or of `ZMod q` when `s` is empty. -/
private noncomputable def draw (s : Finset (ZMod q)) : PMF (ZMod q) :=
  if h : s.Nonempty then PMF.uniformOfFinset s h else PMF.uniformOfFintype (ZMod q)

private theorem draw_of_nonempty {s : Finset (ZMod q)} (h : s.Nonempty) :
    draw s = PMF.uniformOfFinset s h := by
  simp only [draw, h, ↓reduceDIte]

private theorem mem_of_mem_support_draw {s : Finset (ZMod q)} (h : s.Nonempty) {y : ZMod q}
    (hy : y ∈ (draw s).support) : y ∈ s := by
  rwa [draw_of_nonempty h, PMF.mem_support_uniformOfFinset_iff] at hy

/-- A list shorter than `q` misses some element of `ZMod q`. -/
private theorem exists_notMem_of_length_lt {l : List (ZMod q)} (h : l.length < q) :
    ∃ y, y ∉ l :=
  let ⟨y, _, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := l.toFinset)
    (t := Finset.univ) ((List.toFinset_card_le l).trans_lt (by rwa [Finset.card_univ, ZMod.card]))
  ⟨y, fun hmem => hy (List.mem_toFinset.mpr hmem)⟩

private theorem length_lt_of_notMem {l : List (ZMod q)} (hl : l.Nodup) {y : ZMod q}
    (hy : y ∉ l) : l.length < q := by
  have := (List.nodup_cons.mpr ⟨hy, hl⟩).length_le_card
  rw [ZMod.card, List.length_cons] at this
  omega

omit [Fintype ι] [DecidableEq ι] in
private theorem freshLabels_nonempty {tab : Tab ι q} (h : tab.length < q) :
    (freshLabels tab).Nonempty := by
  obtain ⟨y, hy⟩ := exists_notMem_of_length_lt (l := tab.map Prod.snd) (by simpa using h)
  exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩

omit [DecidableEq ι] in
private theorem freshValues_nonempty (x : ι → ZMod q) {tab : Tab ι q} (h : tab.length < q) :
    (freshValues x tab).Nonempty := by
  obtain ⟨y, hy⟩ :=
    exists_notMem_of_length_lt (l := tab.map fun e => ev x e.1) (by simpa using h)
  exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩

omit [DecidableEq ι] in
private theorem freshConsts_nonempty {tab : Tab ι q} (h : tab.length < q) :
    (freshConsts tab).Nonempty := by
  obtain ⟨b, hb⟩ := exists_notMem_of_length_lt (l := tab.map fun e => e.1.2) (by simpa using h)
  refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hmem => hb ?_⟩⟩
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
  exact List.mem_map.mpr ⟨e, he, by rw [heq]⟩

omit [DecidableEq ι] in
/-- An unused value is an unused constant: the constant form `(0, y)` takes the value `y`. -/
private theorem freshValues_subset_freshConsts (x : ι → ZMod q) (tab : Tab ι q) :
    freshValues x tab ⊆ freshConsts tab := by
  intro y hy
  simp only [freshValues, freshConsts, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  intro hmem
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
  exact hy (List.mem_map.mpr ⟨e, he, by rw [heq, ev_zero_left]⟩)

omit [DecidableEq ι] in
/-- For an unused constant `b`, the constant form `(0, b)` clashes exactly when `b` is a used
value. -/
private theorem clash_iff_notMem_freshValues {x : ι → ZMod q} {tab : Tab ι q} {b : ZMod q}
    (hb : b ∈ freshConsts tab) : Clash x tab (0, b) ↔ b ∉ freshValues x tab := by
  simp only [freshConsts, freshValues, Finset.mem_filter, Finset.mem_univ, true_and,
    not_not] at hb ⊢
  constructor
  · rintro ⟨e, he, -, heq⟩
    exact List.mem_map.mpr ⟨e, he, by rw [heq, ev_zero_left]⟩
  · intro hmem
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
    refine ⟨e, he, fun hK => hb (List.mem_map.mpr ⟨e, he, hK⟩), by rw [heq, ev_zero_left]⟩

omit [DecidableEq ι] in
private theorem unusedRange_rep (x : ι → ZMod q) (tab : Tab ι q) :
    RandomPermutation.unusedRange (rep x tab) = freshLabels tab := by
  ext y
  simp only [RandomPermutation.unusedRange, freshLabels, Finset.mem_filter, Finset.mem_univ,
    true_and, RandomPermutation.invLookup_eq_none_iff, rep, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, not_exists, not_and]

omit [DecidableEq ι] in
private theorem unusedDomain_rep (x : ι → ZMod q) (tab : Tab ι q) :
    RandomPermutation.unusedDomain (rep x tab) = freshValues x tab := by
  ext y
  simp only [RandomPermutation.unusedDomain, freshValues, Finset.mem_filter, Finset.mem_univ,
    true_and, RandomPermutation.lookup_eq_none_iff, rep, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, not_exists, not_and]

private theorem answer_forward_of_some {c : RandomPermutation.Cache (ZMod q)} {y z : ZMod q}
    (h : c.lookup y = some z) :
    RandomPermutation.answer (.forward y) c = PMF.pure (z, c) := by
  simp only [RandomPermutation.answer, h]

private theorem answer_forward_of_none {c : RandomPermutation.Cache (ZMod q)} {y : ZMod q}
    (h : c.lookup y = none) :
    RandomPermutation.answer (.forward y) c =
      (draw (RandomPermutation.unusedRange c)).map fun z => (z, (y, z) :: c) := by
  simp only [RandomPermutation.answer, h, draw]
  split_ifs <;> rfl

private theorem answer_inverse_of_some {c : RandomPermutation.Cache (ZMod q)} {y z : ZMod q}
    (h : RandomPermutation.invLookup c z = some y) :
    RandomPermutation.answer (.inverse z) c = PMF.pure (y, c) := by
  simp only [RandomPermutation.answer, h]

private theorem answer_inverse_of_none {c : RandomPermutation.Cache (ZMod q)} {z : ZMod q}
    (h : RandomPermutation.invLookup c z = none) :
    RandomPermutation.answer (.inverse z) c =
      (draw (RandomPermutation.unusedDomain c)).map fun y => (y, (y, z) :: c) := by
  simp only [RandomPermutation.answer, h, draw]
  split_ifs <;> rfl

/-! #### The two handlers -/

/-- One step of the symbolic handler, with its flag. A known key or label gets its entry. A new
key gets a uniform unused label; a new label gets a uniform new constant form. The flag records
that the new key agrees at `x` with a key already in the table. -/
private noncomputable def symStep (x : ι → ZMod q) :
    (p : Prim ι q) → Tab ι q → PMF (PrimSpec ι q p × (Tab ι q × Bool))
  | .fwd K, tab =>
    match tab.lookup K with
    | some ℓ => PMF.pure (ℓ, tab, false)
    | none => (draw (freshLabels tab)).map fun ℓ =>
        (ℓ, (K, ℓ) :: tab, ((rep x tab).lookup (ev x K)).isSome)
  | .inv ℓ, tab =>
    match keyOf tab ℓ with
    | some K => PMF.pure (K, tab, false)
    | none => (draw (freshConsts tab)).map fun b =>
        (((0 : ι → ZMod q), b), ((0, b), ℓ) :: tab, decide (Clash x tab (0, b)))

/-- One step of the real handler, with its flag. It differs from `symStep` only where the flag is
raised: a new key whose value at `x` is already taken gets that value's label, and a new constant
whose value is already taken is redrawn among the unused values. -/
private noncomputable def realStep (x : ι → ZMod q) :
    (p : Prim ι q) → Tab ι q → PMF (PrimSpec ι q p × (Tab ι q × Bool))
  | .fwd K, tab =>
    match tab.lookup K with
    | some ℓ => PMF.pure (ℓ, tab, false)
    | none =>
      match (rep x tab).lookup (ev x K) with
      | some ℓ => PMF.pure (ℓ, tab, true)
      | none => (draw (freshLabels tab)).map fun ℓ => (ℓ, (K, ℓ) :: tab, false)
  | .inv ℓ, tab =>
    match keyOf tab ℓ with
    | some K => PMF.pure (K, tab, false)
    | none => (draw (freshConsts tab)).bind fun b =>
        if Clash x tab (0, b) then
          (draw (freshValues x tab)).map fun b' =>
            (((0 : ι → ZMod q), b'), ((0, b'), ℓ) :: tab, true)
        else PMF.pure (((0 : ι → ZMod q), b), ((0, b), ℓ) :: tab, false)

/-- The symbolic handler without its flag. It does not depend on `x`. -/
private noncomputable def symOracle : (p : Prim ι q) → StateT (Tab ι q) PMF (PrimSpec ι q p)
  | .fwd K => fun tab =>
    match tab.lookup K with
    | some ℓ => PMF.pure (ℓ, tab)
    | none => (draw (freshLabels tab)).map fun ℓ => (ℓ, (K, ℓ) :: tab)
  | .inv ℓ => fun tab =>
    match keyOf tab ℓ with
    | some K => PMF.pure (K, tab)
    | none => (draw (freshConsts tab)).map fun b => (((0 : ι → ZMod q), b), ((0, b), ℓ) :: tab)

/-! #### One step of each handler -/

omit [DecidableEq ι] in
/-- A forward step of the real handler, read at `x`, is a forward query to the lazy permutation. -/
private theorem realStep_fwd_map {x : ι → ZMod q} {tab : Tab ι q}
    (hval : (tab.map fun e => ev x e.1).Nodup) (K : (ι → ZMod q) × ZMod q) :
    (realStep x (.fwd K) tab).map (fun y => (y.1, rep x y.2.1)) =
      RandomPermutation.answer (.forward (ev x K)) (rep x tab) := by
  rcases h₁ : tab.lookup K with _ | ℓ
  · rcases h₂ : (rep x tab).lookup (ev x K) with _ | ℓ
    · simp only [realStep, h₁, h₂, PMF.map_comp, answer_forward_of_none h₂, unusedRange_rep]
      rfl
    · simp only [realStep, h₁, h₂, PMF.pure_map, answer_forward_of_some h₂]
  · simp only [realStep, h₁, PMF.pure_map, answer_forward_of_some (lookup_rep_of_lookup hval h₁)]

omit [DecidableEq ι] in
/-- An inverse step of the real handler, read at `x`, is an inverse query to the lazy
permutation: a redrawn constant is uniform among the unused values (`PMF.unifOn_rehash_eq`). -/
private theorem realStep_inv_map {x : ι → ZMod q} {tab : Tab ι q} (hcon : Consistent x tab)
    (ℓ : ZMod q) :
    (realStep x (.inv ℓ) tab).map (fun y => (ev x y.1, rep x y.2.1)) =
      RandomPermutation.answer (.inverse ℓ) (rep x tab) := by
  rcases h : keyOf tab ℓ with _ | K
  · have hinv : RandomPermutation.invLookup (rep x tab) ℓ = none := by
      rw [invLookup_rep, h]; rfl
    have hlen : tab.length < q := by
      simpa using length_lt_of_notMem hcon.2 (keyOf_eq_none_iff.mp h)
    have hc := freshConsts_nonempty hlen
    have hv := freshValues_nonempty x hlen
    rw [answer_inverse_of_none hinv, unusedDomain_rep, draw_of_nonempty hv,
      ← PMF.unifOn_rehash_eq (freshValues_subset_freshConsts x tab) hc hv, PMF.map_bind]
    simp only [realStep, h, draw_of_nonempty hc, PMF.map_bind]
    refine PMF.bind_congr_on_support _ _ _ fun b hb => ?_
    rw [PMF.mem_support_uniformOfFinset_iff] at hb
    by_cases hcl : Clash x tab (0, b)
    · have hbv : b ∉ freshValues x tab := (clash_iff_notMem_freshValues hb).mp hcl
      rw [ite_eq_left hcl, ite_eq_right hbv, draw_of_nonempty hv, PMF.map_comp]
      congr 1
      funext b'
      simp [rep_cons, ev_zero_left]
    · have hbv : b ∈ freshValues x tab :=
        not_not.mp (mt (clash_iff_notMem_freshValues hb).mpr hcl)
      rw [ite_eq_right hcl, ite_eq_left hbv, PMF.pure_map, PMF.pure_map]
      simp [rep_cons, ev_zero_left]
  · have hinv : RandomPermutation.invLookup (rep x tab) ℓ = some (ev x K) := by
      rw [invLookup_rep, h]; rfl
    simp only [realStep, h, PMF.pure_map, answer_inverse_of_some hinv]

omit [DecidableEq ι] in
/-- The real handler keeps tables consistent. -/
private theorem consistent_of_mem_support_realStep {x : ι → ZMod q} {tab : Tab ι q}
    (hcon : Consistent x tab) (p : Prim ι q) {y : PrimSpec ι q p × (Tab ι q × Bool)}
    (hy : y ∈ (realStep x p tab).support) : Consistent x y.2.1 := by
  cases p with
  | fwd K =>
    rcases h₁ : tab.lookup K with _ | ℓ
    · rcases h₂ : (rep x tab).lookup (ev x K) with _ | ℓ
      · simp only [realStep, h₁, h₂, PMF.mem_support_map_iff] at hy
        obtain ⟨ℓ, hℓ, rfl⟩ := hy
        have hK : ev x K ∉ tab.map fun e => ev x e.1 := by
          intro hmem
          obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
          exact lookup_eq_none_iff'.mp h₂ (ev x e.1, e.2) (List.mem_map.mpr ⟨e, he, rfl⟩) heq
        have hlen : tab.length < q := by simpa using length_lt_of_notMem hcon.1 hK
        have hℓ' := mem_of_mem_support_draw (freshLabels_nonempty hlen) hℓ
        simp only [freshLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ'
        exact ⟨List.nodup_cons.mpr ⟨hK, hcon.1⟩, List.nodup_cons.mpr ⟨hℓ', hcon.2⟩⟩
      · exact ((PMF.mem_support_pure_iff _ _).mp (by simpa [realStep, h₁, h₂] using hy)).symm ▸ hcon
    · exact ((PMF.mem_support_pure_iff _ _).mp (by simpa [realStep, h₁] using hy)).symm ▸ hcon
  | inv ℓ =>
    rcases h : keyOf tab ℓ with _ | K
    · have hℓ : ℓ ∉ tab.map Prod.snd := keyOf_eq_none_iff.mp h
      have hlen : tab.length < q := by simpa using length_lt_of_notMem hcon.2 hℓ
      simp only [realStep, h, PMF.mem_support_bind_iff] at hy
      obtain ⟨b, hb, hy⟩ := hy
      have hb' := mem_of_mem_support_draw (freshConsts_nonempty hlen) hb
      obtain ⟨b₀, _, rfl, hv⟩ : ∃ b₀ flag, y = ((0, b₀), ((0, b₀), ℓ) :: tab, flag) ∧
          b₀ ∈ freshValues x tab := by
        by_cases hcl : Clash x tab (0, b)
        · rw [ite_eq_left hcl, PMF.mem_support_map_iff] at hy
          obtain ⟨b', hb'', rfl⟩ := hy
          exact ⟨b', true, rfl, mem_of_mem_support_draw (freshValues_nonempty x hlen) hb''⟩
        · rw [ite_eq_right hcl, PMF.mem_support_pure_iff] at hy
          subst hy
          exact ⟨b, false, rfl, not_not.mp (mt (clash_iff_notMem_freshValues hb').mpr hcl)⟩
      simp only [freshValues, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact ⟨List.nodup_cons.mpr ⟨by simpa [ev_zero_left] using hv, hcon.1⟩,
        List.nodup_cons.mpr ⟨hℓ, hcon.2⟩⟩
    · exact ((PMF.mem_support_pure_iff _ _).mp (by simpa [realStep, h] using hy)).symm ▸ hcon

omit [NeZero q] [Fintype ι] [DecidableEq ι] in
/-- An outcome with a lowered flag has probability zero under a distribution that always raises
it. -/
private theorem apply_eq_zero_of_flag {β : Type} {p : PMF (β × (Tab ι q × Bool))}
    (hp : ∀ y ∈ p.support, y.2.2 = true) (a : β) (tab' : Tab ι q) :
    p (a, (tab', false)) = 0 :=
  (PMF.apply_eq_zero_iff _ _).mpr fun hmem => by simpa using hp _ hmem

omit [DecidableEq ι] in
/-- The real and symbolic steps give every outcome with a lowered flag the same probability. -/
private theorem realStep_agree (x : ι → ZMod q) (p : Prim ι q) (tab : Tab ι q)
    (a : PrimSpec ι q p) (tab' : Tab ι q) :
    realStep x p tab (a, (tab', false)) = symStep x p tab (a, (tab', false)) := by
  cases p with
  | fwd K =>
    rcases h₁ : tab.lookup K with _ | ℓ
    · rcases h₂ : (rep x tab).lookup (ev x K) with _ | ℓ
      · simp only [realStep, symStep, h₁, h₂, Option.isSome_none]
      · simp only [realStep, symStep, h₁, h₂, Option.isSome_some]
        rw [apply_eq_zero_of_flag (by simp) a tab', apply_eq_zero_of_flag (by simp) a tab']
    · simp only [realStep, symStep, h₁]
  | inv ℓ =>
    rcases h : keyOf tab ℓ with _ | K
    · simp only [realStep, symStep, h]
      rw [PMF.bind_apply, ← PMF.bind_pure_comp _ (draw (freshConsts tab)), PMF.bind_apply]
      refine tsum_congr fun b => congrArg _ ?_
      by_cases hcl : Clash x tab (0, b)
      · simp only [hcl, ↓reduceIte, Function.comp_apply, decide_true]
        rw [apply_eq_zero_of_flag (by simp) a tab', apply_eq_zero_of_flag (by simp) a tab']
      · simp only [hcl, ↓reduceIte, Function.comp_apply, decide_false]
    · simp only [realStep, symStep, h]

omit [DecidableEq ι] in
/-- Dropping the flag of the symbolic step leaves `symOracle`. -/
private theorem symStep_map_fst (x : ι → ZMod q) (p : Prim ι q) (tab : Tab ι q) :
    (symStep x p tab).map (Prod.map id Prod.fst) = symOracle p tab := by
  cases p with
  | fwd K =>
    rcases h₁ : tab.lookup K with _ | ℓ <;>
      simp [symStep, symOracle, h₁, PMF.map_comp, Function.comp_def]
  | inv ℓ =>
    rcases h : keyOf tab ℓ with _ | K <;>
      simp [symStep, symOracle, h, PMF.map_comp, Function.comp_def]

omit [DecidableEq ι] in
/-- The symbolic step only adds to the table, and raises its flag only when the new table has two
distinct keys that agree at `x`. -/
private theorem symStep_support {x : ι → ZMod q} {tab : Tab ι q} (p : Prim ι q)
    {y : PrimSpec ι q p × (Tab ι q × Bool)} (hy : y ∈ (symStep x p tab).support) :
    (∀ e ∈ tab, e ∈ y.2.1) ∧ (y.2.2 = true → HasImageCollision (ev x) y.2.1) := by
  cases p with
  | fwd K =>
    rcases h₁ : tab.lookup K with _ | ℓ
    · simp only [symStep, h₁, PMF.mem_support_map_iff] at hy
      obtain ⟨ℓ, -, rfl⟩ := hy
      refine ⟨fun e he => List.mem_cons_of_mem _ he, fun hflag => ?_⟩
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hflag
      obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_of_lookup_eq_some hm)
      simp only [Prod.mk.injEq] at heq
      exact ⟨e, List.mem_cons_of_mem _ he, (K, ℓ), List.mem_cons_self,
        lookup_eq_none_iff'.mp h₁ e he, heq.1⟩
    · simp only [symStep, h₁, PMF.mem_support_pure_iff] at hy
      subst hy
      exact ⟨fun e he => he, fun h => absurd h (by simp)⟩
  | inv ℓ =>
    rcases h : keyOf tab ℓ with _ | K
    · simp only [symStep, h, PMF.mem_support_map_iff] at hy
      obtain ⟨b, -, rfl⟩ := hy
      refine ⟨fun e he => List.mem_cons_of_mem _ he, fun hflag => ?_⟩
      obtain ⟨e, he, hne, heq⟩ := of_decide_eq_true hflag
      exact ⟨e, List.mem_cons_of_mem _ he, ((0, b), ℓ), List.mem_cons_self, hne, heq⟩
    · simp only [symStep, h, PMF.mem_support_pure_iff] at hy
      subst hy
      exact ⟨fun e he => he, fun h => absurd h (by simp)⟩

omit [DecidableEq ι] in
/-- A raised flag of the symbolic handler means that two distinct keys agree at `x`. -/
private theorem symFlag_preserve (x : ι → ZMod q) (p : Prim ι q) (s : Tab ι q × Bool)
    (hs : s.2 = true → HasImageCollision (ev x) s.1) (a : PrimSpec ι q p) (s' : Tab ι q × Bool)
    (h : (a, s') ∈ (withBadFlag (symStep x) p s).support) :
    s'.2 = true → HasImageCollision (ev x) s'.1 := by
  obtain ⟨tab, b⟩ := s
  simp only [withBadFlag, PMF.mem_support_map_iff, Prod.map, id, Prod.mk.injEq] at h
  obtain ⟨y, hy, -, rfl⟩ := h
  obtain ⟨hsub, hflag⟩ := symStep_support p hy
  exact fun hb => (Bool.or_eq_true_iff.mp hb).elim (fun h => (hs h).mono hsub) hflag

omit [DecidableEq ι] in
/-- The symbolic step adds at most one entry. -/
private theorem length_le_of_mem_support_symOracle (p : Prim ι q) (tab : Tab ι q)
    (a : PrimSpec ι q p) (tab' : Tab ι q) (h : (a, tab') ∈ (symOracle p tab).support) :
    tab'.length ≤ tab.length + 1 := by
  cases p with
  | fwd K =>
    cases h₁ : tab.lookup K <;>
      simp only [symOracle, h₁, PMF.mem_support_map_iff, PMF.mem_support_pure_iff,
        Prod.mk.injEq] at h
    · obtain ⟨_, -, -, rfl⟩ := h
      exact le_rfl
    · exact h.2 ▸ Nat.le_succ _
  | inv ℓ =>
    cases h₂ : keyOf tab ℓ <;>
      simp only [symOracle, h₂, PMF.mem_support_map_iff, PMF.mem_support_pure_iff,
        Prod.mk.injEq] at h
    · obtain ⟨_, -, -, rfl⟩ := h
      exact le_rfl
    · exact h.2 ▸ Nat.le_succ _

end Tables

/-! #### Group queries as primitive queries -/

/-- The key of the form `c₁ K₁ + c₂ K₂`. -/
private def comb (c₁ : ZMod q) (K₁ : (ι → ZMod q) × ZMod q) (c₂ : ZMod q)
    (K₂ : (ι → ZMod q) × ZMod q) : (ι → ZMod q) × ZMod q :=
  (c₁ • K₁.1 + c₂ • K₂.1, c₁ * K₁.2 + c₂ * K₂.2)

omit [DecidableEq ι] in
private theorem ev_comb (x : ι → ZMod q) (c₁ c₂ : ZMod q) (K₁ K₂ : (ι → ZMod q) × ZMod q) :
    ev x (comb c₁ K₁ c₂ K₂) = c₁ * ev x K₁ + c₂ * ev x K₂ := by
  simp only [ev, comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]
  ring

/-- The key of an input: the form `1` for the generator (`none`), the form `X i` for the input
`some i`. -/
private def startKey : Option ι → (ι → ZMod q) × ZMod q
  | none => (0, 1)
  | some i => (Pi.single i 1, 0)

/-- The value at `x` of the input `o`. -/
private def startVal (x : ι → ZMod q) : Option ι → ZMod q
  | none => 1
  | some i => x i

private theorem ev_startKey (x : ι → ZMod q) (o : Option ι) :
    ev x (startKey o) = startVal x o := by
  cases o with
  | none => simp [ev, startKey, startVal]
  | some i => simp [ev, startKey, startVal, Pi.single_apply]

/-- A group query as primitive queries: a labeling query asks for the label of a constant form; a
group operation asks for the keys of its two labels, then for the label of the combined key. -/
private def toPrim : (query : GroupQuery q (ZMod q)) →
    OracleComp (PrimSpec ι q) (GroupOracleSpec q (ZMod q) query)
  | .label β => OracleComp.query (spec := PrimSpec ι q) (.fwd (0, β))
  | .op ℓ₁ ℓ₂ c₁ c₂ => do
    let K₁ ← OracleComp.query (spec := PrimSpec ι q) (.inv ℓ₁)
    let K₂ ← OracleComp.query (spec := PrimSpec ι q) (.inv ℓ₂)
    let ℓ ← OracleComp.query (spec := PrimSpec ι q) (.fwd (comb c₁ K₁ c₂ K₂))
    return some ℓ

/-- A group query as queries to a permutation used as labeling: a labeling query evaluates it; a
group operation inverts it on the two labels and evaluates it on the combination. -/
private def toPerm : (query : GroupQuery q (ZMod q)) →
    OracleComp (RandomPermutation.PermOracleSpec (ZMod q)) (GroupOracleSpec q (ZMod q) query)
  | .label β => OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q)) (.forward β)
  | .op ℓ₁ ℓ₂ c₁ c₂ => do
    let y₁ ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q)) (.inverse ℓ₁)
    let y₂ ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q)) (.inverse ℓ₂)
    let ℓ ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q))
      (.forward (c₁ * y₁ + c₂ * y₂))
    return some ℓ

/-- The adversary `D` on primitive queries: its generator and inputs are the labels of the forms
`1` and `X i`, and each of its outputs is read as the key of that label. -/
private noncomputable def primGame
    (D : ZMod q → (ι → ZMod q) → OracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))) :
    OracleComp (PrimSpec ι q) (γ × (κ → (ι → ZMod q) × ZMod q)) := do
  let u ← tabulateM (R := ZMod q)
    (fun o => OracleComp.query (spec := PrimSpec ι q) (.fwd (startKey o)))
    (Finset.univ : Finset (Option ι)).toList
  let out ← OracleComp.interpret toPrim (D (u none) fun i => u (some i))
  let F ← tabulateM (R := (ι → ZMod q) × ZMod q)
    (fun k => OracleComp.query (spec := PrimSpec ι q) (.inv (out.2 k)))
    (Finset.univ : Finset κ).toList
  return (out.1, F)

/-- The adversary `D` on permutation queries: its generator and inputs are the labels of `1` and
`x i`, and each of its outputs is read as the preimage of that label. -/
private noncomputable def permGame (x : ι → ZMod q)
    (D : ZMod q → (ι → ZMod q) → OracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))) :
    OracleComp (RandomPermutation.PermOracleSpec (ZMod q)) (γ × (κ → ZMod q)) := do
  let u ← tabulateM (R := ZMod q)
    (fun o => OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q))
      (.forward (startVal x o)))
    (Finset.univ : Finset (Option ι)).toList
  let out ← OracleComp.interpret toPerm (D (u none) fun i => u (some i))
  let v ← tabulateM (R := ZMod q)
    (fun k => OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q))
      (.inverse (out.2 k)))
    (Finset.univ : Finset κ).toList
  return (out.1, v)

/-- `primGame D` makes at most `3T + |ι| + 1 + |κ|` primitive queries: one for each input, at
most three for each group query, and one for each output. -/
private theorem isQueryBounded_primGame {T : ℕ}
    {D : ZMod q → (ι → ZMod q) → OracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))}
    (hD : ∀ g u, (D g u).IsQueryBounded T) :
    (primGame D).IsQueryBounded (3 * T + Fintype.card ι + 1 + Fintype.card κ) := by
  have hquery (p : Prim ι q) : (OracleComp.query (spec := PrimSpec ι q) p).IsQueryBounded 1 :=
    IsCostBounded.query p
  have htoPrim : ∀ query : GroupQuery q (ZMod q),
      (toPrim (ι := ι) query).IsQueryBounded ((fun _ : GroupQuery q (ZMod q) => 3) query) := fun
    | .label _ => (hquery _).mono (by norm_num)
    | .op _ _ _ _ => ((hquery _).bind fun _ => (hquery _).bind fun _ =>
        (hquery _).bind fun _ => IsCostBounded.pure _ 0).mono (by norm_num)
  have hD' (g : ZMod q) (u : ι → ZMod q) :
      IsCostBounded (fun _ : GroupQuery q (ZMod q) => 3) (D g u) (T * 3) :=
    (hD g u).isCostBounded_mul_of_forall_le fun _ => le_rfl
  have h := (isQueryBounded_tabulateM (R := ZMod q) (fun o => hquery (.fwd (startKey o)))
    (Finset.univ : Finset (Option ι)).toList).bind fun u =>
      (IsCostBounded.interpret htoPrim (hD' (u none) fun i => u (some i))).bind fun out =>
        (isQueryBounded_tabulateM (R := (ι → ZMod q) × ZMod q) (fun k => hquery (.inv (out.2 k)))
          (Finset.univ : Finset κ).toList).bind fun F => IsCostBounded.pure (out.1, F) 0
  simp only [Finset.length_toList, Finset.card_univ, Fintype.card_option] at h
  exact h.mono (by omega)

/-- Against a permutation `σ`, the permutation queries of `toPerm` answer as the group oracle of
`σ`. -/
private theorem interpret_evalPerm_toPerm (σ : Equiv.Perm (ZMod q))
    (query : GroupQuery q (ZMod q)) :
    OracleComp.interpret (fun p => PMF.pure (RandomPermutation.evalPerm σ p)) (toPerm query) =
      PMF.pure (answer σ query) := by
  cases query with
  | label β =>
    simp [toPerm]
  | op ℓ₁ ℓ₂ c₁ c₂ =>
    obtain ⟨β₁, rfl⟩ := σ.surjective ℓ₁
    obtain ⟨β₂, rfl⟩ := σ.surjective ℓ₂
    simp [toPerm, answer_op_label σ.injective, Probability.PMF.monad_bind_eq_bind]

/-- Against a permutation `σ`, `permGame x D` runs `D` on the labels `σ 1` and `σ (x i)` against
the group oracle of `σ` and reads its outputs through `σ.symm`. -/
private theorem interpret_evalPerm_permGame (σ : Equiv.Perm (ZMod q)) (x : ι → ZMod q)
    (D : ZMod q → (ι → ZMod q) → OracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))) :
    OracleComp.interpret (fun p => PMF.pure (RandomPermutation.evalPerm σ p)) (permGame x D) =
      (OracleComp.interpret (fun query => PMF.pure (answer σ query))
        (D (σ 1) fun i => σ (x i))).map fun out => (out.1, fun k => σ.symm (out.2 k)) := by
  have hu := interpret_tabulateM_pure (spec := RandomPermutation.PermOracleSpec (ZMod q))
    (R := ZMod q) (fun p => PMF.pure (RandomPermutation.evalPerm σ p))
    (fun o => OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q))
      (.forward (startVal x o))) (fun o => σ (startVal x o)) (fun o => by simp)
    (Finset.univ : Finset (Option ι)).toList
  have hv (out : γ × (κ → ZMod q)) :=
    interpret_tabulateM_pure (spec := RandomPermutation.PermOracleSpec (ZMod q)) (R := ZMod q)
      (fun p => PMF.pure (RandomPermutation.evalPerm σ p))
      (fun k => OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q))
        (.inverse (out.2 k))) (fun k => σ.symm (out.2 k)) (fun k => by simp)
      (Finset.univ : Finset κ).toList
  simp only [permGame, interp_norm, pmf_norm, hu, hv, OracleComp.interpret_interpret,
    interpret_evalPerm_toPerm]
  simp only [Finset.mem_toList, Finset.mem_univ, ite_true, startVal]
  exact PMF.bind_pure_comp _ _

section Games

variable [NeZero q]

omit [DecidableEq ι] in
private theorem consistent_of_mem_support_withBadFlag {x : ι → ZMod q} {s : Tab ι q × Bool}
    (hs : Consistent x s.1) (p : Prim ι q) {y : PrimSpec ι q p × (Tab ι q × Bool)}
    (h : y ∈ (withBadFlag (realStep x) p s).support) : Consistent x y.2.1 := by
  obtain ⟨tab, b⟩ := s
  simp only [withBadFlag, PMF.mem_support_map_iff] at h
  obtain ⟨z, hz, rfl⟩ := h
  exact (consistent_of_mem_support_realStep hs p hz :)

omit [DecidableEq ι] in
private theorem realFl_fwd_map {x : ι → ZMod q} {s : Tab ι q × Bool} (hs : Consistent x s.1)
    (K : (ι → ZMod q) × ZMod q) :
    ((withBadFlag (realStep x) (.fwd K)).run s).map (fun y => (y.1, rep x y.2.1)) =
      (RandomPermutation.answer (.forward (ev x K))).run (rep x s.1) := by
  obtain ⟨tab, b⟩ := s
  simp only [StateT.run, withBadFlag, PMF.map_comp]
  exact realStep_fwd_map hs.1 K

omit [DecidableEq ι] in
private theorem realFl_inv_map {x : ι → ZMod q} {s : Tab ι q × Bool} (hs : Consistent x s.1)
    (ℓ : ZMod q) :
    ((withBadFlag (realStep x) (.inv ℓ)).run s).map (fun y => (ev x y.1, rep x y.2.1)) =
      (RandomPermutation.answer (.inverse ℓ)).run (rep x s.1) := by
  obtain ⟨tab, b⟩ := s
  simp only [StateT.run, withBadFlag, PMF.map_comp]
  exact realStep_inv_map hs ℓ

omit [DecidableEq ι] in
/-- The real handler on one group query, read at `x`, is the lazy permutation on that query. -/
private theorem realGroup_step (x : ι → ZMod q) (query : GroupQuery q (ZMod q))
    (s : Tab ι q × Bool) (hs : Consistent x s.1) :
    ((OracleComp.interpret (withBadFlag (realStep x)) (toPrim query)).run s).map
        (fun y => (y.1, rep x y.2.1)) =
      (OracleComp.interpret RandomPermutation.answer (toPerm query)).run (rep x s.1) := by
  cases query with
  | label β =>
    simpa only [toPrim, toPerm, OracleComp.interpret_query, ev_zero_left] using
      realFl_fwd_map hs (0, β)
  | op ℓ₁ ℓ₂ c₁ c₂ =>
    let r (s : Tab ι q × Bool) := rep x s.1
    let I (s : Tab ι q × Bool) : Prop := Consistent x s.1
    simp only [toPrim, toPerm, interp_norm, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure]
    refine map_bind_eq_of_step (ev x) id r I (realFl_inv_map hs ℓ₁)
      (fun _ hy => consistent_of_mem_support_withBadFlag hs _ hy) _ _ fun K₁ s₁ hs₁ => ?_
    refine map_bind_eq_of_step (ev x) id r I (realFl_inv_map hs₁ ℓ₂)
      (fun _ hy => consistent_of_mem_support_withBadFlag hs₁ _ hy) _ _ fun K₂ s₂ hs₂ => ?_
    refine map_bind_eq_of_step id id r (fun _ => True)
      (ev_comb x c₁ c₂ K₁ K₂ ▸ realFl_fwd_map hs₂ (comb c₁ K₁ c₂ K₂))
      (fun _ _ => trivial) _ _ fun _ _ _ => ?_
    simp only [PMF.pure_map, id]

/-- The real handler on `primGame D`, read at `x`, is the lazy permutation on `permGame x D`. -/
private theorem real_eq_lazy (x : ι → ZMod q)
    (D : ZMod q → (ι → ZMod q) → OracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))) :
    ((OracleComp.interpret (withBadFlag (realStep x)) (primGame D)).run ([], false)).map
        (fun r => ((r.1.1, fun k => ev x (r.1.2 k)), rep x r.2.1)) =
      (OracleComp.interpret RandomPermutation.answer (permGame x D)).run [] := by
  let r (s : Tab ι q × Bool) := rep x s.1
  let I (s : Tab ι q × Bool) : Prop := Consistent x s.1
  let ψ (b : γ × (κ → (ι → ZMod q) × ZMod q)) := (b.1, fun k => ev x (b.2 k))
  have hpres : ∀ (p : Prim ι q) (s : Tab ι q × Bool), I s →
      ∀ a s', (a, s') ∈ (withBadFlag (realStep x) p s).support → I s' :=
    fun p s hs _ _ h => consistent_of_mem_support_withBadFlag hs p h
  have hgroup (g : ZMod q) (u : ι → ZMod q) (s : Tab ι q × Bool) (hs : I s) :
      ((OracleComp.interpret (withBadFlag (realStep x))
          (OracleComp.interpret toPrim (D g u))).run s).map (fun y => (y.1, r y.2)) =
        (OracleComp.interpret RandomPermutation.answer
          (OracleComp.interpret toPerm (D g u))).run (r s) := by
    rw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
    exact OracleComp.run_interpret_map_state_of_invariant _ _ r I
      (fun query s hs a s' h =>
        OracleComp.run_interpret_invariant _ _ hpres (toPrim query) s hs a s' h)
      (fun query s hs => realGroup_step x query s hs) (D g u) s hs
  have h0 : I ([], false) := ⟨List.nodup_nil, List.nodup_nil⟩
  simp only [primGame, permGame, interp_norm, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure]
  refine map_bind_eq_of_step (fun (t : Option ι → ZMod q) o => id (t o)) ψ r I
    (map_run_tabulateM _ _ _ _ id rfl r I hpres
      (fun o s hs => by
        simpa only [OracleComp.interpret_query, id, ev_startKey] using
          realFl_fwd_map hs (startKey o))
      _ ([], false) h0)
    (fun y hy => OracleComp.run_interpret_invariant _ _ hpres _ ([], false) h0 y.1 y.2 hy) _ _ ?_
  intro u s₁ hs₁
  dsimp only [id]
  refine map_bind_eq_of_step id ψ r I (hgroup (u none) (fun i => u (some i)) s₁ hs₁)
    (fun y hy => OracleComp.run_interpret_invariant _ _
      (fun query s hs a s' h =>
        OracleComp.run_interpret_invariant _ _ hpres (toPrim query) s hs a s' h)
      (D (u none) fun i => u (some i)) s₁ hs₁ y.1 y.2
      (by rwa [OracleComp.interpret_interpret] at hy)) _ _ ?_
  intro out s₂ hs₂
  dsimp only [id]
  refine map_bind_eq_of_step (fun (t : κ → (ι → ZMod q) × ZMod q) k => ev x (t k)) ψ r I
    (map_run_tabulateM _ _ _ _ (ev x) (by simp [ev]) r I hpres
      (fun k s hs => by simpa only [OracleComp.interpret_query] using realFl_inv_map hs (out.2 k))
      _ s₂ hs₂)
    (fun y hy => OracleComp.run_interpret_invariant _ _ hpres _ s₂ hs₂ y.1 y.2 hy) _ _ ?_
  intro F s₃ _
  rw [PMF.pure_map]

/-- With a uniform permutation as labeling, the group oracle is the real handler on primitive
queries. -/
private theorem uniform_interpret_eq_real (x : ι → ZMod q)
    (D : ZMod q → (ι → ZMod q) → OracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))) :
    (PMF.uniformOfFintype (Equiv.Perm (ZMod q))).bind (fun σ =>
        (OracleComp.interpret (fun query => PMF.pure (answer σ query))
          (D (σ 1) fun i => σ (x i))).map fun out => (out.1, fun k => σ.symm (out.2 k))) =
      ((OracleComp.interpret (withBadFlag (realStep x)) (primGame D)).run ([], false)).map
        fun r => (r.1.1, fun k => ev x (r.1.2 k)) := by
  simpa only [Probability.PMF.monad_bind_eq_bind, interpret_evalPerm_permGame,
    ← real_eq_lazy x D, PMF.map_comp, Function.comp_def] using
    RandomPermutation.uniform_interpret_eq_lazy (permGame x D)

/-- The game against a deterministic adversary with a uniform permutation as labeling. -/
private noncomputable def detGame (W : (ι → ZMod q) → γ → (κ → ZMod q) → Bool)
    (D : ZMod q → (ι → ZMod q) → OracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))) :
    Game :=
  (PMF.uniformOfFintype (Equiv.Perm (ZMod q))).bind fun σ =>
    (PMF.uniformOfFintype (ι → ZMod q)).bind fun x =>
      (OracleComp.interpret (fun query => PMF.pure (answer σ query))
        (D (σ 1) fun i => σ (x i))).bind fun out => PMF.pure (W x out.1 fun k => σ.symm (out.2 k))

/-- The game against a deterministic adversary is the real handler on `primGame D`, averaged over
`x`. -/
private theorem detGame_eq (W : (ι → ZMod q) → γ → (κ → ZMod q) → Bool)
    (D : ZMod q → (ι → ZMod q) → OracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))) :
    detGame W D = (PMF.uniformOfFintype (ι → ZMod q)).bind fun x =>
      ((OracleComp.interpret (withBadFlag (realStep x)) (primGame D)).run ([], false)).bind
        fun r => PMF.pure (W x r.1.1 fun k => ev x (r.1.2 k)) := by
  unfold detGame
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun x => ?_)
  calc _ = ((PMF.uniformOfFintype (Equiv.Perm (ZMod q))).bind fun σ =>
          (OracleComp.interpret (fun query => PMF.pure (answer σ query))
            (D (σ 1) fun i => σ (x i))).map fun out => (out.1, fun k => σ.symm (out.2 k))).bind
            fun r => PMF.pure (W x r.1 r.2) := by
        simp only [PMF.bind_bind, PMF.bind_map]; rfl
    _ = _ := by
        rw [uniform_interpret_eq_real, PMF.bind_map]; rfl

/-- For a fixed `x`, the real game is won at most as often as the symbolic one, plus the
probability that the symbolic table has two distinct keys that agree at `x`. -/
private theorem real_le (x : ι → ZMod q) (W : (ι → ZMod q) → γ → (κ → ZMod q) → Bool)
    (D : ZMod q → (ι → ZMod q) → OracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))) :
    ((OracleComp.interpret (withBadFlag (realStep x)) (primGame D)).run ([], false)).bind
        (fun r => PMF.pure (W x r.1.1 fun k => ev x (r.1.2 k))) true ≤
      ((OracleComp.interpret symOracle (primGame D)).run []).bind
          (fun y => PMF.pure (W x y.1.1 fun k => ev x (y.1.2 k))) true +
        ((OracleComp.interpret symOracle (primGame D)).run []).bind
          (fun y => PMF.pure (decide (HasImageCollision (ev x) y.2))) true := by
  have hiub := OracleComp.identicalUntilBad_withBadFlag (realStep x) (symStep x)
    (realStep_agree x)
  have hfst := OracleComp.run_interpret_withBadFlag_map_fst (symStep x) symOracle
    (symStep_map_fst x) (primGame D) [] false
  refine (hiub.bind_apply_le (primGame D) ([], false) _ true).trans ?_
  rw [hiub.bad_eq, ← hfst, PMF.bind_map, PMF.bind_map]
  refine add_le_add le_rfl (le_of_le_of_eq ?_ (PMF.bind_pure_decide_apply_true _
    (fun y : (γ × (κ → (ι → ZMod q) × ZMod q)) × (Tab ι q × Bool) =>
      HasImageCollision (ev x) y.2.1)).symm)
  refine PMF.toOuterMeasure_mono _ fun y hy => ?_
  exact OracleComp.run_interpret_invariant (withBadFlag (symStep x))
    (fun s => s.2 = true → HasImageCollision (ev x) s.1) (symFlag_preserve x)
    (primGame D) ([], false) (by simp) y.1 y.2 hy.2 hy.1

end Games

/-- Distinct keys from a set of `n` keys agree at a uniform point with probability at most
`n.choose 2 / q`. -/
private theorem toOuterMeasure_pairs_le [NeZero q] (hq : q.Prime)
    (s : Finset ((ι → ZMod q) × ZMod q)) :
    (PMF.uniformOfFintype (ι → ZMod q)).toOuterMeasure
      {x | ∃ K ∈ s, ∃ K' ∈ s, K ≠ K' ∧ ev x K = ev x K'} ≤ (s.card.choose 2 : ℝ≥0∞) / q := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert K s hK ih =>
    have hc : ((insert K s).card.choose 2 : ℝ≥0∞) / q =
        (s.card.choose 2 : ℝ≥0∞) / q + (s.card : ℝ≥0∞) / q := by
      rw [Finset.card_insert_of_notMem hK, Nat.choose_succ_succ', Nat.choose_one_right,
        ← ENNReal.add_div, Nat.cast_add, add_comm]
    rw [hc]
    have hsub : {x : ι → ZMod q | ∃ a ∈ insert K s, ∃ b ∈ insert K s, a ≠ b ∧ ev x a = ev x b} ⊆
        {x | ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ev x a = ev x b} ∪ ⋃ K' ∈ s, {x | ev x K = ev x K'} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, Finset.mem_insert] at hx
      obtain ⟨a, ha, b, hb, hab, heq⟩ := hx
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact Or.inr ⟨b, hb, heq⟩
      · exact Or.inr ⟨a, ha, heq.symm⟩
      · exact Or.inl ⟨a, ha, b, hb, hab, heq⟩
    refine (MeasureTheory.measure_mono hsub).trans ((MeasureTheory.measure_union_le _ _).trans
      (add_le_add ih ((MeasureTheory.measure_biUnion_finset_le _ _).trans ?_)))
    calc ∑ K' ∈ s, (PMF.uniformOfFintype (ι → ZMod q)).toOuterMeasure {x | ev x K = ev x K'}
        ≤ ∑ _K' ∈ s, 1 / (q : ℝ≥0∞) := Finset.sum_le_sum fun K' hK' =>
          toOuterMeasure_uniform_linearForm_eq_le hq fun h => hK (h ▸ hK')
      _ = (s.card : ℝ≥0∞) / q := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- A table with `n` entries has two distinct keys that agree at a uniform point with probability
at most `n.choose 2 / q`. -/
private theorem toOuterMeasure_collides_le [NeZero q] (hq : q.Prime) (tab : Tab ι q) :
    (PMF.uniformOfFintype (ι → ZMod q)).toOuterMeasure {x | HasImageCollision (ev x) tab} ≤
      (tab.length.choose 2 : ℝ≥0∞) / q := by
  let s := (tab.map Prod.fst).toFinset
  have hsub : {x | HasImageCollision (ev x) tab} ⊆
      {x | ∃ K ∈ s, ∃ K' ∈ s, K ≠ K' ∧ ev x K = ev x K'} := by
    intro x hx
    change ∃ K ∈ s, ∃ K' ∈ s, K ≠ K' ∧ ev x K = ev x K'
    simpa only [s, List.mem_toFinset] using (hasImageCollision_iff (ev x) tab).mp hx
  have hcard : s.card ≤ tab.length :=
    (List.toFinset_card_le (tab.map Prod.fst)).trans_eq (List.length_map _)
  refine (MeasureTheory.measure_mono hsub).trans ((toOuterMeasure_pairs_le hq s).trans ?_)
  gcongr

/-- A test that holds on at most an `ε` fraction of the points holds at a uniform point with
probability at most `ε`. -/
private theorem uniform_bind_apply_true_le [NeZero q] {E : (ι → ZMod q) → Bool} {ε : ℝ≥0}
    (h : (((Finset.univ.filter fun x => E x).card : ℕ) : ℝ≥0) ≤ ε * (q : ℝ≥0) ^ Fintype.card ι) :
    ((PMF.uniformOfFintype (ι → ZMod q)).bind fun x => PMF.pure (E x)) true ≤ ε := by
  classical
  have hq0 : (q : ℝ≥0∞) ^ Fintype.card ι ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne q))
  have hqt : (q : ℝ≥0∞) ^ Fintype.card ι ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top q)
  have hE := PMF.bind_pure_decide_apply_true (PMF.uniformOfFintype (ι → ZMod q)) fun x => E x = true
  simp only [Bool.decide_eq_true] at hE
  rw [hE, PMF.toOuterMeasure_uniformOfFintype, Fintype.card_fun, ZMod.card, Nat.cast_pow,
    ← div_eq_mul_inv, ENNReal.div_le_iff hq0 hqt]
  simp only [Set.mem_ofPred_eq]
  exact_mod_cast h

omit [DecidableEq κ] in
/-- **The core bound for deterministic adversaries.** The symbolic table ends with at most
`3T + |ι| + 1 + |κ|` keys, so two distinct keys agree at `x` with probability at most
`C(3T + |ι| + 1 + |κ|, 2) / q`; the keys of the outputs do not depend on `x`, so the hypothesis on
`W` bounds the symbolic game by `ε`. -/
private theorem detGame_apply_le [NeZero q] (hq : q.Prime) {T : ℕ}
    (W : (ι → ZMod q) → γ → (κ → ZMod q) → Bool)
    {D : ZMod q → (ι → ZMod q) → OracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))}
    (hD : ∀ g u, (D g u).IsQueryBounded T) (ε : ℝ≥0)
    (hW : ∀ (o : γ) (F : κ → (ι → ZMod q) × ZMod q),
      (((Finset.univ.filter fun x : ι → ZMod q =>
        W x o fun k => ∑ i, (F k).1 i * x i + (F k).2).card : ℕ) : ℝ≥0) ≤
          ε * (q : ℝ≥0) ^ Fintype.card ι) :
    detGame W D true ≤
      (((3 * T + Fintype.card ι + 1 + Fintype.card κ).choose 2 : ℕ) : ℝ≥0∞) / q + ε := by
  classical
  rw [detGame_eq]
  set symRun := (OracleComp.interpret symOracle (primGame D)).run ([] : Tab ι q)
  have hlen : ∀ y ∈ symRun.support,
      y.2.length ≤ 3 * T + Fintype.card ι + 1 + Fintype.card κ := fun y hy => by
    simpa using (isQueryBounded_primGame hD).measure_le symOracle List.length
      (fun p s res s' h => length_le_of_mem_support_symOracle p s res s' h) (s := []) hy
  calc _ ≤ ((PMF.uniformOfFintype (ι → ZMod q)).bind fun x =>
          symRun.bind fun y => PMF.pure (W x y.1.1 fun k => ev x (y.1.2 k))) true +
        ((PMF.uniformOfFintype (ι → ZMod q)).bind fun x =>
          symRun.bind fun y => PMF.pure (decide (HasImageCollision (ev x) y.2))) true :=
        PMF.bind_apply_le_add_on_support _ true fun x _ => real_le x W D
    _ ≤ (ε : ℝ≥0∞) +
        (((3 * T + Fintype.card ι + 1 + Fintype.card κ).choose 2 : ℕ) : ℝ≥0∞) / q := by
        rw [PMF.bind_comm, PMF.bind_comm (PMF.uniformOfFintype (ι → ZMod q))]
        refine add_le_add (PMF.bind_apply_le_on_support _ fun y _ => ?_)
          (PMF.bind_apply_le_on_support _ fun y hy => ?_)
        · exact uniform_bind_apply_true_le (hW y.1.1 y.1.2)
        · rw [PMF.bind_pure_decide_apply_true _
            (fun x : ι → ZMod q => HasImageCollision (ev x) y.2)]
          refine (toOuterMeasure_collides_le hq y.2).trans ?_
          gcongr
          exact hlen y hy
    _ = _ := add_comm _ _

/-- The replies of the group oracle on labels in `ZMod q` form a finite type. -/
private instance [NeZero q] (query : GroupQuery q (ZMod q)) :
    Fintype (GroupOracleSpec q (ZMod q) query) := by
  cases query
  · exact inferInstanceAs (Fintype (ZMod q))
  · exact inferInstanceAs (Fintype (Option (ZMod q)))

omit [Fintype κ] [DecidableEq κ] in
/-- Fixing the adversary's coins for each pair of inputs makes the game an average of games against
deterministic adversaries. -/
private theorem permLinearGame_eq_bind_detGame [NeZero q]
    (W : (ι → ZMod q) → γ → (κ → ZMod q) → Bool)
    (B : ZMod q → (ι → ZMod q) →
      ProbOracleComp (GroupOracleSpec q (ZMod q)) (γ × (κ → ZMod q))) :
    permLinearGame W B =
      (Probability.PMF.pi fun gu : ZMod q × (ι → ZMod q) =>
        ProbOracleComp.coinLaw (B gu.1 gu.2)).bind fun Ω =>
          detGame W fun g u => ProbOracleComp.fixCoins (B g u) (Ω (g, u)) := by
  have key (σ : Equiv.Perm (ZMod q)) (g : ZMod q) (u : ι → ZMod q) :
      runLabeled (σ : ZMod q → ZMod q) (B g u) =
        (Probability.PMF.pi fun gu : ZMod q × (ι → ZMod q) =>
          ProbOracleComp.coinLaw (B gu.1 gu.2)).bind fun Ω =>
            OracleComp.interpret (fun query => PMF.pure (answer σ query))
              (ProbOracleComp.fixCoins (B g u) (Ω (g, u))) := by
    unfold runLabeled
    rw [← ProbOracleComp.bind_interpret_fixCoins (B g u) (answer σ),
      ← Probability.PMF.pi_map_eval (fun gu : ZMod q × (ι → ZMod q) =>
        ProbOracleComp.coinLaw (B gu.1 gu.2)) (g, u),
      PMF.bind_map]
    rfl
  unfold permLinearGame detGame
  simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, key,
    PMF.bind_bind]
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype (ι → ZMod q))]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Equiv.Perm (ZMod q)))]

/-! ### The bound -/

/-- **Bound for games with linear inputs.** For prime `q`, suppose that for every output value
`o` and every choice of linear forms `F k` for the outputs, `W` holds on at most an `ε` fraction of
the points. Then an adversary that makes at most `T` queries to the group oracle on every path wins
the game with linear inputs with probability at most `C(3T + |ι| + 1 + |κ|, 2) / q + ε`. -/
theorem succProbability_linearGame_le [NeZero q] [Fintype S] [DecidableEq S]
    [Nonempty (ZMod q ↪ S)] (hq : q.Prime) {T : ℕ} (W : (ι → ZMod q) → γ → (κ → ZMod q) → Bool)
    {A : S → (ι → S) → ProbOracleComp (GroupOracleSpec q S) (γ × (κ → S))}
    (hA : ∀ g u, (A g u).IsQueryBounded T) (ε : ℝ≥0)
    (hW : ∀ (o : γ) (F : κ → (ι → ZMod q) × ZMod q),
      (((Finset.univ.filter fun x : ι → ZMod q =>
        W x o fun k => ∑ i, (F k).1 i * x i + (F k).2).card : ℕ) : ℝ≥0) ≤
          ε * (q : ℝ≥0) ^ Fintype.card ι) :
    (linearGame W A).succProbability ≤
      (((3 * T + Fintype.card ι + 1 + Fintype.card κ).choose 2 : ℕ) : ℝ≥0) / q + ε := by
  have hq0 : (q : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hle : linearGame W A true ≤
      (((((3 * T + Fintype.card ι + 1 + Fintype.card κ).choose 2 : ℕ) : ℝ≥0) / q + ε : ℝ≥0) :
        ℝ≥0∞) := by
    refine (linearGame_le_bind_permLinearGame W A).trans
      (PMF.bind_apply_le_on_support _ fun j _ => ?_)
    rw [permLinearGame_eq_bind_detGame]
    refine PMF.bind_apply_le_on_support _ fun Ω _ => ?_
    refine (detGame_apply_le hq W (fun g u => ProbOracleComp.isQueryBounded_fixCoins
      (isQueryBounded_relabelOut j hA g u) _) ε hW).trans_eq ?_
    rw [ENNReal.coe_add, ENNReal.coe_div hq0, ENNReal.coe_natCast, ENNReal.coe_natCast]
  exact (ENNReal.toNNReal_mono ENNReal.coe_ne_top hle).trans_eq (ENNReal.toNNReal_coe _)

end Cslib.Crypto.GenericGroup
