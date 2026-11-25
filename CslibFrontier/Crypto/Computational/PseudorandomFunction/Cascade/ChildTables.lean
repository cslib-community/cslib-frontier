/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.Hybrid
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixHybrid.Independent
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixHybrid.Split
import CslibFrontier.Probability.PMF.Uniform

/-!
# Child-function games for adjacent cascade hybrids

The two neighboring cascade hybrids use the same short-label table and the same query
responder. For a longer query, the responder evaluates the next block using the child
function at its parent prefix, then continues evaluating the remaining suffix. In the
old-depth game each child function is the base family under an independent parent key.
In the new-depth game each child function is an independent uniform random function.

These are eager, distribution-level endpoint laws for the adjacent-hybrid step of
[BonehShoup2023], v0.6, Sections 4.6.1 (printed pp. 152–154) and 6.4.2 (printed pp. 229–230).
The laws identify the child-function distribution that the adaptive reduction will replace.
-/

public section

namespace Cslib.Crypto

open Probability

/-- Run the cascade client with prescribed child-function distribution and independent uniform
labels for words ending at or before the old depth. Invalid queries receive the empty word. -/
@[expose]
noncomputable def cascadeChildTableGame (valid : ℕ → List Bool → Bool)
    (inLen : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n depth : ℕ)
    [Fintype {word : List Bool // word.length ≤ depth * inLen n}]
    (children : PMF (BitString (depth * inLen n) → BitString (inLen n) → BitString n)) :
    PMF Bool :=
  (PMF.uniformOfFintype ({word : List Bool // word.length ≤ depth * inLen n} → BitString n)).bind
    fun short => children.bind fun child =>
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun request => PMF.pure (if valid n request.2 then
          prefixHybridSplitAnswer (cascadeFamily inLen family) short child request.2 else [])))
        (adversary n [])

private theorem cascadeFamily_oneBlock {inLen : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool} {key block : List Bool}
    (hwidth : 0 < inLen key.length) (hblock : block.length = inLen key.length) :
    cascadeFamily inLen family key block = family key block := by
  have hrows : BitString.listRows 1 (inLen key.length) block = [block] := by
    simpa [BitString.listRows] using BitString.listRows_succ_append 0 _ hblock []
  rw [cascadeFamily, hblock, Nat.div_self hwidth, hrows]
  rfl

private theorem add_width_le_of_dvd {width depth length : ℕ} (hdvd : width ∣ length)
    (hdepth : depth * width < length) : depth * width + width ≤ length := by
  obtain ⟨blocks, rfl⟩ := hdvd
  rw [← Nat.succ_mul, Nat.mul_comm width blocks]
  exact Nat.mul_le_mul_right width <| Nat.lt_of_not_ge fun h =>
    hdepth.not_ge (by simpa only [Nat.mul_comm width blocks] using Nat.mul_le_mul_right width h)

private theorem realChildAnswer_eq {inLen : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool} {valid : List Bool → Bool} {n depth : ℕ}
    (hwidth : 0 < inLen n)
    (hlen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (short parents : {word : List Bool // word.length ≤ depth * inLen n} → BitString n)
    (query : List Bool) (hv : valid query = true) (ha : inLen n ∣ query.length) :
    prefixHybridIndependentLabelOracle valid (cascadeFamily inLen family) short parents query =
      prefixHybridSplitAnswer (width := inLen n) (cascadeFamily inLen family) short
        (fun parent block => BitString.ofList n
          (family (List.ofFn (parents ⟨List.ofFn parent, by simp⟩)) (List.ofFn block))) query := by
  let cut := depth * inLen n
  by_cases h : cut < query.length
  · rw [prefixHybridSplitAnswer_of_lt_length h]
    have hcut : cut + inLen n ≤ query.length := add_width_le_of_dvd ha h
    have hparent : List.ofFn (BitString.ofList cut query) = query.take cut := by
      rw [← BitString.ofList_take]
      exact BitString.ofFn_ofList (by simp [Nat.min_eq_left h.le])
    let block := (query.drop cut).take (inLen n)
    have hblock : block.length = inLen n := by
      simp only [block, List.length_take, List.length_drop]
      omega
    have hbits : List.ofFn (BitString.ofList (inLen n) (query.drop cut)) = block := by
      rw [← BitString.ofList_take]
      exact BitString.ofFn_ofList hblock
    have hsplit : block ++ query.drop (cut + inLen n) = query.drop cut := by
      rw [← List.drop_drop]
      exact List.take_append_drop _ _
    let key := List.ofFn (parents ⟨query.take cut,
      (List.length_take ..).trans_le (Nat.min_le_left ..)⟩)
    have hkey : key.length = n := List.length_ofFn
    have hbase : (family key block).length = n :=
      (hlen key block (by rw [hkey, hblock])).trans hkey
    have hrem : inLen n ∣ (query.drop (cut + inLen n)).length := by
      rw [List.length_drop]
      exact Nat.dvd_sub ha (dvd_add (Nat.dvd_mul_left _ _) (dvd_refl _))
    simp only [prefixHybridIndependentLabelOracle, hv, ↓reduceIte,
      show depth * inLen n < query.length from h, hparent, hbits]
    change cascadeFamily inLen family key (query.drop cut) =
      cascadeFamily inLen family (List.ofFn (BitString.ofList n (family key block)))
        (query.drop (cut + inLen n))
    rw [BitString.ofFn_ofList hbase, ← hsplit,
      cascadeFamily_append hlen key (by rwa [hkey])
        (by rw [hkey, hblock])
        (by rwa [hkey]),
      cascadeFamily_oneBlock (key := key) (block := block) (by rwa [hkey]) (by rw [hkey, hblock])]
  · have hs : query.length ≤ depth * inLen n := Nat.le_of_not_gt h
    rw [prefixHybridSplitAnswer_of_length_le hs]
    simp [prefixHybridIndependentLabelOracle, hv, show ¬ depth * inLen n < query.length from h,
      List.take_of_length_le hs, List.drop_eq_nil_of_le hs]

/-- In the real child-function world, independent parent keys reproduce the previous cascade
hybrid for a prefix-free client. The domain uses whole blocks, and the base family preserves
key width on such blocks. -/
theorem eval_cascadePrefixHybridGame_eq_childTables_real (valid : ℕ → List Bool → Bool)
    (inLen : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n depth : ℕ)
    [Fintype {word : List Bool // word.length ≤ depth * inLen n}]
    (hwidth : 0 < inLen n) (halign : ∀ query, valid n query = true → inLen n ∣ query.length)
    (hlen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (hpf : IsPrefixFreeOn (valid n) n (adversary n [])) :
    ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n depth) =
      cascadeChildTableGame valid inLen family adversary n depth
        ((PMF.uniformOfFintype (BitString (depth * inLen n) → BitString n)).map fun keys =>
          fun parent block => BitString.ofList n
            (family (List.ofFn (keys parent)) (List.ofFn block))) := by
  let cut := depth * inLen n
  let Word := {word : List Bool // word.length ≤ cut}
  let encodeParent : BitString cut ↪ Word :=
    ⟨fun parent => ⟨List.ofFn parent, by simp⟩,
      fun _ _ h => List.ofFn_injective (congrArg Subtype.val h)⟩
  have hparents := PMF.uniformOfFintype_pi_map_comp_embedding (α := BitString n) encodeParent
  rw [cascadePrefixHybridGame, eval_prefixHybridGame_eq_independentLabels _ _ _ _ _
    (fun key word hk => (length_cascadeFamily hlen key word).trans hk) hpf]
  have horacle (short parents : Word → BitString n) (query : List Bool) :
      prefixHybridIndependentLabelOracle (valid n) (cascadeFamily inLen family)
        short parents query =
        if valid n query then
          prefixHybridSplitAnswer (width := inLen n) (cascadeFamily inLen family) short
            (fun parent block => BitString.ofList n
              (family (List.ofFn (parents (encodeParent parent))) (List.ofFn block))) query
        else [] := by
    cases hv : valid n query
    · simp [prefixHybridIndependentLabelOracle, hv]
    · simp only [↓reduceIte]
      exact realChildAnswer_eq hwidth hlen short parents query hv (halign query hv)
  rw [cascadeChildTableGame, ← hparents, PMF.map_comp, ← PMF.uniformOfFintype_prod, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def, horacle]
  rfl

/-- Independent uniform child functions reproduce the next cascade hybrid on aligned queries. -/
theorem eval_cascadePrefixHybridGame_succ_eq_childTables_ideal (valid : ℕ → List Bool → Bool)
    (inLen : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n depth : ℕ)
    [Fintype {word : List Bool // word.length ≤ depth * inLen n}]
    (hwidth : 0 < inLen n) (halign : ∀ query, valid n query = true → inLen n ∣ query.length) :
    ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n (depth + 1)) =
      cascadeChildTableGame valid inLen family adversary n depth
        (PMF.uniformOfFintype
          (BitString (depth * inLen n) → BitString (inLen n) → BitString n)) := by
  rw [cascadePrefixHybridGame, Nat.succ_mul, eval_prefixHybridGame_add_eq_split _ _ _ _ _ _
    hwidth (cascadeFamily_nil inLen family)
    (fun query hv h => add_width_le_of_dvd (halign query hv) h)]
  rw [← PMF.uniformOfFintype_prod, PMF.bind_bind]
  simp [cascadeChildTableGame, PMF.bind_map, Function.comp_def]

end Cslib.Crypto
