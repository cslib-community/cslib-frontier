/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TreeSignature.Reduction
public import CslibFrontier.Probability.PMF.Coupling
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.SuppCases

/-!
# Shared leaf-guarded signing handler combinators

Common `PMF`-level state-handler infrastructure shared by the two security reduction hops of
`TreeSignature.scheme`:

* `CslibFrontier.Crypto.Computational.TreeSignature.IdealToLazy` (replacing random-function coins
  with lazy node keys and edge signatures).
* `CslibFrontier.Crypto.Computational.TreeSignature.LazyToIndexed` (coupling lazy node keys with a
  pre-sampled planted-key table).

Keeping these leaf-guarded handler combinators in a dedicated topic module isolates `PMF.Coupling`
and its support machinery from `Reduction` and `ForgerEfficiency`.

## Main definitions

* `Cslib.Crypto.TreeSignature.TreeState`, `Cslib.Crypto.TreeSignature.TreeBody`: wrapped handler
  state (`σ × TreeLog`) and leaf-signing body type.
* `Cslib.Crypto.TreeSignature.guardedTreeHandler`: leaf-collision-guarded wrapper around a
  `TreeBody`.
* `Cslib.Crypto.TreeSignature.lazySignBody`: `PMF`-level body of `lazySignHandler`.

## Main results

* `Cslib.Crypto.TreeSignature.guardedTreeHandler_bind_comm`: lift a `PMF.HiddenCoupling` across
  `guardedTreeHandler`.
* `Cslib.Crypto.TreeSignature.guardedTreeHandler_map`: lift a `PMF.RepInv` across
  `guardedTreeHandler`.
* `Cslib.Crypto.TreeSignature.guardedTreeHandler_support_inv`: invariant preservation for
  `guardedTreeHandler`.
* `Cslib.Crypto.TreeSignature.eval_lazySignHandler_eq`: semantic equality between
  `lazySignHandler` and `guardedTreeHandler` on `lazySignBody`.
-/

public section

namespace Cslib.Crypto

open Probability

namespace TreeSignature

/-- Full handler state pairing an algorithm-specific cache `σ` with `TreeLog`. -/
abbrev TreeState (σ : Type) := σ × TreeLog

/-- Inner leaf-signing body parameterized by the cache state `σ`. -/
abbrev TreeBody (σ : Type) := List Bool → List Bool → σ → PMF (List Bool × σ)

/-- Leaf-collision-guarded `PMF` signing handler: accepts `n`-bit messages, aborts with `[]` once a
leaf repeats, and otherwise delegates signing to `body`. -/
@[expose] noncomputable def guardedTreeHandler {σ : Type} (depth : ℕ → ℕ) (n : ℕ)
    (body : TreeBody σ) (req : Unit × List Bool) : StateT (TreeState σ) PMF (List Bool) :=
  fun (inner, ⟨queried, seenLeaves, bad⟩) =>
    if req.2.length = n then
      if bad then PMF.pure ([], (inner, ⟨req.2 :: queried, seenLeaves, true⟩))
      else (BitString.uniformList (depth n)).bind fun leaf =>
        if seenLeaves.contains leaf then
          PMF.pure ([], (inner, ⟨req.2 :: queried, seenLeaves, true⟩))
        else (body leaf req.2 inner).map fun (sig, inner') =>
          (sig, (inner', ⟨req.2 :: queried, leaf :: seenLeaves, false⟩))
    else PMF.pure ([], (inner, ⟨req.2 :: queried, seenLeaves, bad⟩))

/-- Lift a `PMF.HiddenCoupling` of two leaf-signing bodies through `guardedTreeHandler`. -/
theorem guardedTreeHandler_bind_comm {σ₁ σ₂ γ : Type} (depth : ℕ → ℕ) (n : ℕ)
    {body₁ : TreeBody σ₁} {body₂ : γ → TreeBody σ₂}
    (exp : σ₁ → PMF γ) (rep : σ₁ → σ₂) (inv : TreeState σ₁ → Prop)
    (req : Unit × List Bool) (inner : σ₁) (queried seen : List (List Bool)) (bad : Bool)
    (hinv_pure : ∀ b', inv (inner, ⟨req.2 :: queried, seen, b'⟩))
    (hgood : req.2.length = n → bad = false →
      ∀ leaf ∈ (BitString.uniformList (depth n)).support, seen.contains leaf = false →
        PMF.HiddenCoupling (body₁ leaf req.2 inner) (exp inner)
          (fun x => exp x.2) (fun x => (x.1, rep x.2))
          (fun k => body₂ k leaf req.2 (rep inner))
          (fun x => inv (x.2, ⟨req.2 :: queried, leaf :: seen, false⟩))) :
    PMF.HiddenCoupling (guardedTreeHandler depth n body₁ req (inner, ⟨queried, seen, bad⟩))
      (exp inner) (fun (_, inner', _) => exp inner') (fun (a, inner', log) => (a, rep inner', log))
      (fun k => guardedTreeHandler depth n (body₂ k) req (rep inner, ⟨queried, seen, bad⟩))
      (fun x => inv x.2) := by
  dsimp only [guardedTreeHandler]
  split_ifs with hmsg hbad
  · exact PMF.HiddenCoupling.pure rfl (fun _ _ => rfl) (hinv_pure true)
  · have hbf : bad = false := Bool.eq_false_iff.mpr hbad
    refine ⟨?_, fun ⟨ans, s'⟩ hm => ?_⟩
    · rw [PMF.bind_bind]
      simp_rw [PMF.map_bind]
      rw [PMF.bind_comm (exp inner) (BitString.uniformList (depth n))]
      refine PMF.bind_congr_on_support _ _ _ fun leaf hl => ?_
      cases hs : seen.contains leaf
      · simp only [Bool.false_eq_true, ↓reduceIte, PMF.bind_map, Function.comp_def]
        simpa only [pmf_norm] using congrArg (PMF.map fun (k, sig, inner') =>
          (k, sig, (inner', TreeLog.mk (req.2 :: queried) (leaf :: seen) false)))
          (hgood hmsg hbf leaf hl hs).bind_eq
      · simp only [↓reduceIte, PMF.pure_bind, PMF.map, Function.comp_def]
    · obtain ⟨leaf, hl, hm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hm
      cases hs : seen.contains leaf
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hm
        supp_cases hm with ⟨⟨sig, inner'⟩, hmem, rfl, rfl⟩
        exact (hgood hmsg hbf leaf hl hs).support_inv (sig, inner') hmem
      · simp only [hs, ↓reduceIte] at hm
        supp_cases hm; exact hinv_pure true
  · exact PMF.HiddenCoupling.pure rfl (fun _ _ => rfl) (hinv_pure bad)

/-- Lift a `PMF.RepInv` simulation of two leaf-signing bodies through `guardedTreeHandler`. -/
theorem guardedTreeHandler_map {σ₁ σ₂ : Type} (depth : ℕ → ℕ) (n : ℕ)
    {body₁ : TreeBody σ₁} {body₂ : TreeBody σ₂}
    (rep : σ₁ → σ₂) (inv : TreeState σ₁ → Prop)
    (req : Unit × List Bool) (inner : σ₁) (queried seen : List (List Bool)) (bad : Bool)
    (hinv_pure : ∀ b', inv (inner, ⟨req.2 :: queried, seen, b'⟩))
    (hgood : req.2.length = n → bad = false →
      ∀ leaf ∈ (BitString.uniformList (depth n)).support, seen.contains leaf = false →
        PMF.RepInv (body₁ leaf req.2 inner) (body₂ leaf req.2 (rep inner))
          (fun (sig, inner') => (sig, rep inner'))
          (fun x => inv (x.2, ⟨req.2 :: queried, leaf :: seen, false⟩))) :
    PMF.RepInv (guardedTreeHandler depth n body₁ req (inner, ⟨queried, seen, bad⟩))
      (guardedTreeHandler depth n body₂ req (rep inner, ⟨queried, seen, bad⟩))
      (fun (ans, inner', log) => (ans, rep inner', log))
      (fun x => inv x.2) := by
  have h := guardedTreeHandler_bind_comm depth n (body₁ := body₁) (body₂ := fun _ : Unit => body₂)
    (fun _ => PMF.pure ()) rep inv req inner queried seen bad hinv_pure fun hm hb leaf hl hs => by
      obtain ⟨heq, hi⟩ := hgood hm hb leaf hl hs
      exact ⟨by rw [PMF.pure_bind, ← heq]; simp only [PMF.map, pmf_norm], hi⟩
  exact ⟨by simpa only [PMF.map, pmf_norm] using congrArg (PMF.map Prod.snd) h.bind_eq,
      h.support_inv⟩

/-- Lift support invariant preservation from a leaf-signing body to `guardedTreeHandler`. -/
theorem guardedTreeHandler_support_inv {σ : Type} (depth : ℕ → ℕ) (n : ℕ)
    (body : TreeBody σ) (inv : TreeState σ → Prop)
    (req : Unit × List Bool) (inner : σ) (queried seen : List (List Bool)) (bad : Bool)
    (hinv_pure : ∀ b', inv (inner, ⟨req.2 :: queried, seen, b'⟩))
    (hgood : req.2.length = n → bad = false →
      ∀ leaf ∈ (BitString.uniformList (depth n)).support, seen.contains leaf = false →
        ∀ sig inner', (sig, inner') ∈ (body leaf req.2 inner).support →
          inv (inner', ⟨req.2 :: queried, leaf :: seen, false⟩)) :
    ∀ ans s', (ans, s') ∈
      (guardedTreeHandler depth n body req (inner, ⟨queried, seen, bad⟩)).support → inv s' :=
  fun ans s' hm => (guardedTreeHandler_map depth n (body₂ := body) id inv req inner queried seen
    bad hinv_pure fun hm' hb leaf hl hs => ⟨PMF.map_id _, fun ⟨sig, inner'⟩ h =>
      hgood hm' hb leaf hl hs sig inner' h⟩).support_inv (ans, s') hm

/-- Leaf-signing body of `lazySignHandler` after evaluating `ProbComp` to `PMF`. -/
@[expose] noncomputable def lazySignBody (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n : ℕ)
    (root : List Bool × List Bool) : TreeBody (NodeKeyCache × EdgeSigCache) :=
  fun leaf msg caches =>
    (ProbComp.eval (certifyLazy S depth n root leaf caches)).bind fun
      ((node, (_, sk), certs), (nodes', edges')) =>
        (ProbComp.eval (memoize (fun _ => S.sign sk (leaf.getLastD false).toNat msg)
          (node, (leaf.getLastD false).toNat) edges')).map fun (σ, edges'') =>
            (encodeSignature leaf certs σ, (nodes', edges''))

/-- `ProbComp.eval` transforms `lazySignHandler` into `guardedTreeHandler` over `lazySignBody`. -/
theorem eval_lazySignHandler_eq (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n : ℕ)
    (root : List Bool × List Bool) (req : Unit × List Bool) (s : LazyTreeState) :
    ProbComp.eval (lazySignHandler S depth n root req s) =
      guardedTreeHandler depth n (lazySignBody S depth n root) req s := by
  obtain ⟨⟨nodes, edges⟩, ⟨queried, seen, bad⟩⟩ := s
  simp only [lazySignHandler, guardedTreeHandler, lazySignBody, apply_ite ProbComp.eval,
    BitString.eval_sampleList, pmf_norm]
  split_ifs with hmsg hbad <;> rfl

end TreeSignature

end Cslib.Crypto
