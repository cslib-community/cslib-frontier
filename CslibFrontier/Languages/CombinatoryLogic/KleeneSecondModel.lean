/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Computability.RecursiveInClockedJoin
public import CslibFrontier.Foundations.Computability.RecursiveInContinuous
public import CslibFrontier.Languages.CombinatoryLogic.PartialCombinatoryAlgebra

/-!
# Kleene's second model

Kleene's second model `K₂` is the partial combinatory algebra on Baire space `ℕ → ℕ` in which an
element `a` acts on `x` as a code for a continuous partial function. Here `a` is read as an oracle
program with a parameter: its first entry `a 0` is the index of an oracle code, and its tail
`a' = n ↦ a (n + 1)` is a parameter oracle. The program runs relative to the join `a' ⊕ x` of the
parameter with the input, and `a ⬝ x` is the function `n ↦ Φ_{a 0}^{a' ⊕ x}(n)`, defined when
every entry is (`Cslib.PartialCombinatoryAlgebra.kleeneTwoEval`).

* *The oracle evaluator.* One fixed code interprets every element: relative to `a ⊕ x`, it
  computes `a ⬝ x` entry by entry (`exists_kleeneTwo_interpreter`), using the universal code for
  total oracles. Equivalently, each entry of `a ⬝ x` is a clocked oracle program over the
  interface of two oracles, run with `a'` and `x` (`kleeneTwoEval_eq_clocked`).
* *Combinators.* `k ⬝ a` is the element running the code `joinLeft` with parameter `a`, which
  returns its parameter. `s ⬝ a ⬝ b` is the element whose parameter is `a ⊕ b` and whose code
  applies, entry by entry, `a ⬝ c` to `b ⬝ c`, through the universal code. Its code first
  evaluates the entries `(a ⬝ c)(n)` and `(b ⬝ c)(n)`, so that it diverges somewhere when `a ⬝ c` or
  `b ⬝ c` does.
* *Continuous functions.* By the continuity theorem
  `Nat.RecursiveIn.Code.continuous_iff_exists_code`, the total maps on Baire space represented in
  `K₂` are exactly the continuous ones (`continuous_iff_exists_kleeneTwo_app`).
* *The computable sub-pca.* The computable elements are closed under application and contain the
  combinators, so they form a sub-pca `K₂^rec` (`kleeneTwoRec`).

## Main definitions

* `Cslib.PartialCombinatoryAlgebra.kleeneTwoEval`: the partial function that `a` computes on `x`.
* `Cslib.PartialCombinatoryAlgebra.kleeneTwoCode`: the element running a code with a parameter.
* `Cslib.PartialCombinatoryAlgebra.kleeneTwo`: Kleene's second model `K₂`.
* `Cslib.PartialCombinatoryAlgebra.kleeneTwoRec`: its sub-pca `K₂^rec` of computable elements.

## Main results

* `Cslib.PartialCombinatoryAlgebra.kleeneTwo_app_eq_some_iff`: application is code evaluation.
* `Cslib.PartialCombinatoryAlgebra.exists_kleeneTwo_interpreter`: one code interprets `K₂`.
* `Cslib.PartialCombinatoryAlgebra.kleeneTwoEval_eq_clocked`: application as a clocked program
  over two oracles.
* `Cslib.PartialCombinatoryAlgebra.continuous_iff_exists_kleeneTwo_app`: the total maps
  represented in `K₂` are the continuous ones.
* `Cslib.PartialCombinatoryAlgebra.computable_of_mem_kleeneTwo_app`: application preserves
  computability, which makes `K₂^rec` a sub-pca.

## Implementation notes

The sources define `K₂` through neighbourhood functions: `a` codes a continuous partial functional
by listing, for each finite sequence, either a value or "look further". Here `a` codes the
functional instead by an oracle program and its parameter, so that application reuses the oracle
code evaluator, the universal code, the join and the clocked oracle programs of
`Foundations/Computability`, and the pca laws are proved through codes rather than by
manipulating neighbourhood functions. For total maps the two presentations represent the same
functionals, the continuous ones (`continuous_iff_exists_kleeneTwo_app`; the neighbourhood-function
side is the standard argument and is not formalized). The two models are not claimed to be
isomorphic as pcas here.

Application is defined pointwise: `a ⬝ x` is defined when the program of `a` converges on `x` at
every entry. The combinators are fixed elements `kleeneTwoCode c (fun _ => 0)` for codes `c`
chosen once, so they are computable, and `K₂^rec` is a sub-pca with the same `k` and `s`.

## References

* [J. van Oosten, *Realizability: An Introduction to its Categorical Side*][vanOosten2008],
  §1.4 (Kleene's second model; the precise locator is to be checked).
* [J. Longley and D. Normann, *Higher-Order Computability*][LongleyNormann2015], §3.2 (Kleene's
  second model and its computable submodel; the subsection numbers are to be checked).
-/

public section

open Encodable Denumerable Nat.RecursiveIn Nat.RecursiveIn.Code

namespace Cslib.PartialCombinatoryAlgebra

/-- The partial function that `a` computes on `x` in Kleene's second model: the oracle code with
index `a 0`, run relative to the join of the tail `n ↦ a (n + 1)` with `x`. -/
@[expose] def kleeneTwoEval (a x : ℕ → ℕ) : ℕ →. ℕ :=
  Code.eval (Partrec.join (fun n => a (n + 1) : ℕ → ℕ) x) (ofNat Code (a 0))

/-- The element of `K₂` running the oracle code `c` with the parameter `p`: its first entry is the
index of `c`, and its tail is `p`. -/
@[expose] def kleeneTwoCode (c : Code) (p : ℕ → ℕ) : ℕ → ℕ :=
  fun n => if n = 0 then encode c else p (n - 1)

@[simp]
theorem kleeneTwoEval_kleeneTwoCode (c : Code) (p x : ℕ → ℕ) :
    kleeneTwoEval (kleeneTwoCode c p) x = Code.eval (Partrec.join p x) c := by
  simp [kleeneTwoEval, kleeneTwoCode]

/-- A partial function defined everywhere, as a total function. -/
private def total (φ : ℕ →. ℕ) : Part (ℕ → ℕ) :=
  ⟨∀ n, (φ n).Dom, fun h n => (φ n).get (h n)⟩

private theorem mem_total {φ : ℕ →. ℕ} {y : ℕ → ℕ} : y ∈ total φ ↔ ∀ n, y n ∈ φ n := by
  refine ⟨fun ⟨h, hy⟩ n => ?_, fun h => ⟨fun n => (h n).1, funext fun n => (h n).2⟩⟩
  subst hy
  exact Part.get_mem (h n)

private theorem total_eq_some_iff {φ : ℕ →. ℕ} {y : ℕ → ℕ} :
    total φ = Part.some y ↔ φ = (y : ℕ →. ℕ) := by
  rw [Part.eq_some_iff, mem_total]
  exact ⟨fun h => funext fun n => Part.eq_some_iff.2 (h n), fun h n => h ▸ Part.mem_some _⟩

/-- Application in Kleene's second model. -/
private def kApp (a x : ℕ → ℕ) : Part (ℕ → ℕ) :=
  total (kleeneTwoEval a x)

/-! ### Codes for the combinators -/

/-- Prepending a number to what a code computes, uniformly in the oracle. -/
private theorem exists_consCode (e : ℕ) (d : Code) :
    ∃ c : Code, ∀ g, Code.eval g c = fun n =>
      if n = 0 then Part.some e else Code.eval g d (n - 1) := by
  have hd : HasUniformCode (id : (ℕ →. ℕ) → ℕ →. ℕ) fun g => Code.eval g d := ⟨d, fun _ => rfl⟩
  have hite := HasUniformCode.ite (b := id) Computable.id (hd.comp (HasUniformCode.of_computable
    (f := fun n => n - 1) (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)).to_comp))
  have hout : Computable fun m : ℕ => if m.unpair.1 = 0 then e else m.unpair.2 :=
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0))
      (Primrec.const e) (Primrec.snd.comp Primrec.unpair)).to_comp
  obtain ⟨c, hc⟩ := (HasUniformCode.of_computable hout).comp
    ((HasUniformCode.of_computable Computable.id).pair hite)
  refine ⟨c, fun g => (hc g).trans (funext fun n => ?_)⟩
  rcases n with _ | n
  · simp [Seq.seq]
  · have hb : (Part.some n >>= Code.eval g d) = Code.eval g d n := Part.bind_some n _
    simp [Seq.seq, Part.bind_some_eq_map, Part.map_map, Function.comp_def, Part.map_id', hb]

/-- A code that prepends `e` to what `d` computes. -/
private noncomputable def consCode (e : ℕ) (d : Code) : Code :=
  Classical.choose (exists_consCode e d)

private theorem eval_consCode {g : ℕ →. ℕ} {d : Code} {q : ℕ → ℕ} (c : Code)
    (hd : Code.eval g d = (q : ℕ →. ℕ)) :
    Code.eval g (consCode (encode c) d) = (kleeneTwoCode c q : ℕ →. ℕ) := by
  refine (Classical.choose_spec (exists_consCode (encode c) d) g).trans (funext fun n => ?_)
  by_cases hn : n = 0 <;> simp [kleeneTwoCode, hn, hd]

/-- The join of two total functions, as a total function. -/
private def joinFun (a b : ℕ → ℕ) : ℕ → ℕ :=
  fun n => cond n.bodd (2 * b n.div2 + 1) (2 * a n.div2)

/-- A universal code for total oracles. -/
private noncomputable def univ : Code :=
  Classical.choose exists_universal

/-- The code that, given codes computing `a` and `x`, computes `a ⬝ x` entry by entry. It first
evaluates both codes at the entry, so that it diverges wherever they do. -/
private noncomputable def apCode (cf cg : Code) : Code :=
  comp right (pair (pair cf cg) (comp (univ.subst (join (comp cf succ) cg))
    (pair (comp cf zero) (pair left right))))

private theorem eval_apCode {h : ℕ →. ℕ} {cf cg : Code} {y z : ℕ → ℕ}
    (hf : Code.eval h cf = (y : ℕ →. ℕ)) (hg : Code.eval h cg = (z : ℕ →. ℕ)) :
    Code.eval h (apCode cf cg) = kleeneTwoEval y z := by
  have hq : Code.eval h (join (comp cf succ) cg) =
      Partrec.join (fun n => y (n + 1) : ℕ → ℕ) z := by
    rw [eval_join, hg]
    congr 1
    funext n
    change (Nat.succ : ℕ →. ℕ) n >>= Code.eval h cf = _
    rw [hf]
    exact Part.bind_some _ _
  funext n
  have hu := Classical.choose_spec exists_universal (joinFun (fun n => y (n + 1)) z) (y 0) n
  have hj : Partrec.join (fun n => y (n + 1) : ℕ → ℕ) z =
      ((joinFun (fun n => y (n + 1)) z : ℕ → ℕ) : ℕ →. ℕ) :=
    Partrec.join_coe _ _
  rw [← hj] at hu
  simp [apCode, Code.eval, hf, hg, eval_subst, hq, Seq.seq, pure, PFun.pure, univ, hu,
    kleeneTwoEval, bind_pfun, Part.bind_some_eq_map, Part.map_map, Function.comp_def, Part.map_id']

private theorem dom_of_dom_apCode {h : ℕ →. ℕ} {cf cg : Code} {n : ℕ}
    (hd : (Code.eval h (apCode cf cg) n).Dom) :
    (Code.eval h cf n).Dom ∧ (Code.eval h cg n).Dom := by
  simp only [apCode, Code.eval] at hd
  obtain ⟨⟨⟨hf, hg⟩, -⟩, -⟩ := hd
  exact ⟨hf, hg⟩

/-- The code of `k`: prepend the index of `joinLeft` to the input. -/
private noncomputable def codeK : Code :=
  consCode (encode joinLeft) joinRight

/-- The code of `s ⬝ a ⬝ b`, run with the parameter `a ⊕ b`: apply `a ⬝ c` to `b ⬝ c`. -/
private noncomputable def codeS₂ : Code :=
  apCode (apCode (joinLeft.subst joinLeft) joinRight) (apCode (joinRight.subst joinLeft) joinRight)

/-- The code of `s ⬝ a`, run with the parameter `a`: prepend the index of `codeS₂` to `a ⊕ b`. -/
private noncomputable def codeS₁ : Code :=
  consCode (encode codeS₂) oracle

/-- The code of `s`: prepend the index of `codeS₁` to the input. -/
private noncomputable def codeS : Code :=
  consCode (encode codeS₁) joinRight

private theorem kApp_eq_some {a x y : ℕ → ℕ} (h : kleeneTwoEval a x = (y : ℕ →. ℕ)) :
    kApp a x = Part.some y :=
  total_eq_some_iff.2 h

private theorem kApp_k (a : ℕ → ℕ) :
    kApp (kleeneTwoCode codeK fun _ => 0) a = Part.some (kleeneTwoCode joinLeft a) :=
  kApp_eq_some <| by
    rw [kleeneTwoEval_kleeneTwoCode]
    exact eval_consCode _ (eval_joinRight _ _)

private theorem kApp_k_a (a b : ℕ → ℕ) : kApp (kleeneTwoCode joinLeft a) b = Part.some a :=
  kApp_eq_some <| by rw [kleeneTwoEval_kleeneTwoCode, eval_joinLeft]

private theorem kApp_s (a : ℕ → ℕ) :
    kApp (kleeneTwoCode codeS fun _ => 0) a = Part.some (kleeneTwoCode codeS₁ a) :=
  kApp_eq_some <| by
    rw [kleeneTwoEval_kleeneTwoCode]
    exact eval_consCode _ (eval_joinRight _ _)

private theorem kApp_s_a (a b : ℕ → ℕ) :
    kApp (kleeneTwoCode codeS₁ a) b = Part.some (kleeneTwoCode codeS₂ (joinFun a b)) :=
  kApp_eq_some <| by
    rw [kleeneTwoEval_kleeneTwoCode]
    exact eval_consCode _ (Partrec.join_coe a b)

private theorem kApp_s_a_b (a b c : ℕ → ℕ) :
    kApp (kleeneTwoCode codeS₂ (joinFun a b)) c = ap kApp (kApp a c) (kApp b c) := by
  have hJ : Partrec.join a b = (joinFun a b : ℕ →. ℕ) := Partrec.join_coe a b
  set h := Partrec.join (joinFun a b) c
  have hL : Code.eval h (joinLeft.subst joinLeft) = (a : ℕ →. ℕ) := by
    rw [eval_subst, eval_joinLeft, ← hJ, eval_joinLeft]
  have hR : Code.eval h (joinRight.subst joinLeft) = (b : ℕ →. ℕ) := by
    rw [eval_subst, eval_joinLeft, ← hJ, eval_joinRight]
  have hC : Code.eval h joinRight = (c : ℕ →. ℕ) := eval_joinRight _ _
  have hA := eval_apCode hL hC
  have hB := eval_apCode hR hC
  have hS : kApp (kleeneTwoCode codeS₂ (joinFun a b)) c = total (Code.eval h codeS₂) := by
    rw [kApp, kleeneTwoEval_kleeneTwoCode]
  rw [hS]
  by_cases hd : (kApp a c).Dom ∧ (kApp b c).Dom
  · obtain ⟨hac, hbc⟩ := hd
    have hy := (total_eq_some_iff.1 (Part.some_get hac).symm)
    have hz := (total_eq_some_iff.1 (Part.some_get hbc).symm)
    rw [← Part.some_get hac, ← Part.some_get hbc, ap_some_some, kApp, codeS₂,
      eval_apCode (hA.trans hy) (hB.trans hz)]
  · have hl : ¬ (total (Code.eval h codeS₂)).Dom := fun hl => hd ⟨fun n => by
      simpa [hA] using (dom_of_dom_apCode (hl n)).1, fun n => by
      simpa [hB] using (dom_of_dom_apCode (hl n)).2⟩
    have hr : ¬ (ap kApp (kApp a c) (kApp b c)).Dom := fun hr => hd ⟨hr.1, hr.2.1⟩
    rw [Part.eq_none_iff'.2 hl, Part.eq_none_iff'.2 hr]

/-- **Kleene's second model** `K₂`: the pca on Baire space in which `a ⬝ x` is the function
`n ↦ Φ_{a 0}^{a' ⊕ x}(n)` computed by the oracle code with index `a 0` relative to the join of the
tail `a'` of `a` with `x`, defined when every entry is. -/
noncomputable def kleeneTwo : PartialCombinatoryAlgebra (ℕ → ℕ) where
  app := kApp
  k := kleeneTwoCode codeK fun _ => 0
  s := kleeneTwoCode codeS fun _ => 0
  ap_ap_k a b := by rw [kApp_k, ap_some_some, kApp_k_a]
  dom_ap_s a b := by
    rw [kApp_s, ap_some_some, kApp_s_a]
    trivial
  ap_ap_ap_s a b c := by rw [kApp_s, ap_some_some, kApp_s_a, ap_some_some, kApp_s_a_b]

/-- `a ⬝ x` has value `y` in `K₂` exactly when the program of `a` computes `y` from `x`. -/
theorem kleeneTwo_app_eq_some_iff {a x y : ℕ → ℕ} :
    kleeneTwo.app a x = Part.some y ↔ kleeneTwoEval a x = (y : ℕ →. ℕ) :=
  total_eq_some_iff

/-- `a ⬝ x` is defined in `K₂` exactly when the program of `a` converges on `x` at every entry. -/
theorem dom_kleeneTwo_app {a x : ℕ → ℕ} :
    (kleeneTwo.app a x).Dom ↔ ∀ n, (kleeneTwoEval a x n).Dom :=
  Iff.rfl

/-- **The interpreter of `K₂`.** One oracle code computes `a ⬝ x` entry by entry, relative to the
join `a ⊕ x` of the element with its argument. -/
theorem exists_kleeneTwo_interpreter :
    ∃ u : Code, ∀ a x : ℕ → ℕ, Code.eval (Partrec.join a x) u = kleeneTwoEval a x :=
  ⟨apCode joinLeft joinRight, fun _ _ => eval_apCode (eval_joinLeft _ _) (eval_joinRight _ _)⟩

/-- Each entry of `a ⬝ x` is a clocked oracle program over the interface of two oracles, run with
the tail of `a` and with `x`: the compiled program of the code of `a`, with its queries to the join
answered by `splitHandler`. -/
theorem kleeneTwoEval_eq_clocked (a x : ℕ → ℕ) (n : ℕ) :
    kleeneTwoEval a x n = ClockedComp.eval
      (OracleComp.sumHandler ((fun n => a (n + 1) : ℕ → ℕ) : ℕ →. ℕ) (x : ℕ →. ℕ))
      (((ofNat Code (a 0)).toClocked n).subst splitHandler) := by
  rw [eval_subst_splitHandler _ _ (stable_toClocked _ _ n), eval_toClocked]
  rfl

/-! ### Continuous functions -/

/-- **The total maps represented in `K₂` are the continuous ones.** A total map `F` on Baire
space is continuous exactly when some element `a` of `K₂` has `a ⬝ x = F x` for every `x`. -/
theorem continuous_iff_exists_kleeneTwo_app {F : (ℕ → ℕ) → ℕ → ℕ} :
    Continuous F ↔ ∃ a, ∀ x, kleeneTwo.app a x = Part.some (F x) := by
  refine ⟨fun hF => ?_, fun ⟨a, ha⟩ => continuous_of_eval (p := fun n => a (n + 1))
    (c := ofNat Code (a 0)) fun x n => congrFun (kleeneTwo_app_eq_some_iff.1 (ha x)) n⟩
  obtain ⟨e, he⟩ := exists_code_continuous
  obtain ⟨p, hp⟩ := he F hF
  exact ⟨kleeneTwoCode e p, fun x => kleeneTwo_app_eq_some_iff.2 <| by
    rw [kleeneTwoEval_kleeneTwoCode]
    exact funext (hp x)⟩

/-! ### The computable sub-pca -/

/-- The element running a code with a computable parameter is computable. -/
theorem computable_kleeneTwoCode (c : Code) {p : ℕ → ℕ} (hp : Computable p) :
    Computable (kleeneTwoCode c p) :=
  (Computable.nat_casesOn Computable.id (Computable.const (encode c))
    (hp.comp Computable.snd).to₂).of_eq fun n => by cases n <;> simp [kleeneTwoCode]

/-- Application in `K₂` preserves computability. -/
theorem computable_of_mem_kleeneTwo_app {a x y : ℕ → ℕ} (ha : Computable a) (hx : Computable x)
    (hy : y ∈ kleeneTwo.app a x) : Computable y := by
  have hJ : Computable (joinFun (fun n => a (n + 1)) x) :=
    Computable.cond (Primrec.nat_bodd.to_comp)
      (Computable.succ.comp ((Primrec.nat_mul.to_comp.comp (Computable.const 2)
        (hx.comp Primrec.nat_div2.to_comp))))
      (Primrec.nat_mul.to_comp.comp (Computable.const 2)
        (ha.comp (Computable.succ.comp Primrec.nat_div2.to_comp)))
  have hev : Code.eval (joinFun (fun n => a (n + 1)) x : ℕ →. ℕ) (ofNat Code (a 0)) = y := by
    have hj : Partrec.join (fun n => a (n + 1) : ℕ → ℕ) x =
        ((joinFun (fun n => a (n + 1)) x : ℕ → ℕ) : ℕ →. ℕ) :=
      Partrec.join_coe _ _
    rw [← hj]
    exact total_eq_some_iff.1 (Part.eq_some_iff.2 hy)
  exact Partrec.nat_iff.2 (Nat.RecursiveIn.partrec_of_oracle
    (fun g hg => (Set.mem_singleton_iff.1 hg) ▸ Partrec.nat_iff.1 hJ)
    (exists_code.2 ⟨_, hev⟩))

/-- **The computable sub-pca `K₂^rec`** of Kleene's second model: the computable elements of
Baire space, with the application of `K₂`. -/
noncomputable def kleeneTwoRec : PartialCombinatoryAlgebra {a : ℕ → ℕ // Computable a} :=
  kleeneTwo.sub (fun a => Computable a) (computable_kleeneTwoCode _ (Computable.const 0))
    (computable_kleeneTwoCode _ (Computable.const 0))
    fun _ _ _ ha hb hc => computable_of_mem_kleeneTwo_app ha hb hc

/-- Application in `K₂^rec` is application in `K₂`. -/
@[simp]
theorem map_val_kleeneTwoRec_app (a b : {a : ℕ → ℕ // Computable a}) :
    (kleeneTwoRec.app a b).map Subtype.val = kleeneTwo.app a b :=
  map_val_sub_app _ _ _ _ _ a b

end Cslib.PartialCombinatoryAlgebra
