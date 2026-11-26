/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Operator.LeastFixedPoint.Tuple

/-!
# Semantics of tuple pullback for least-fixed-point formulas

The full-tuple compiler preserves truth, including nested least fixed points and captured
parameters. The proof transports all candidate relations through the tuple bijection; it
therefore also preserves the total pre-fixed-intersection semantics of unchecked syntax.
-/

public section

open FirstOrder Language

namespace Cslib.Logic.FO.LFP.Tuple

variable {L L' : Language} {d : ℕ}

open Operator.Tuple

variable {M N : Type} [L.Structure M] [L'.Structure N]
  (f : FOMap L L' d) (e : (Fin d → M) ≃ N)
  (hf : ∀ {α : Type} (φ : L'.Formula α) (v : α × Fin d → M),
    (f φ).Realize v ↔ φ.Realize (fun a => e (fun i => v (a, i))))

private theorem append_singleton {Γ : List ℕ} {A : Type} {k : ℕ}
    (R : Set (Fin k → A)) (ρ : Operator.RelEnv Γ A) :
    @Operator.RelEnv.append Γ [k] A (@Operator.RelEnv.cons [] A k R
      (@Operator.RelEnv.empty A)) ρ = @Operator.RelEnv.cons Γ A k R ρ := by
  funext n r
  cases r <;> rfl

private theorem realize_lfp_prefixed {A : Type} [L.Structure A] {Γ : List ℕ}
    {α : Type} {k : ℕ} (body : RawFormula L (k :: Γ) (α ⊕ Fin k))
    (args : Fin k → L.Term α) (ρ : Operator.RelEnv Γ A) (v : α → A) :
    (lfp body args).Realize interpretation ρ v ↔
      ∀ R : Set (Fin k → A),
        (∀ xs, body.Realize interpretation (Operator.RelEnv.cons R ρ)
          (Sum.elim v xs) → xs ∈ R) → (fun i => (args i).realize v) ∈ R := by
  simp only [lfp, Operator.Formula.Realize, interpretation, append_singleton]
  rfl

/-- An element bijection carries the intersection of all pre-fixed relations to that of the
conjugate operator. Monotonicity is not needed for this raw semantic identity. -/
private theorem prefixed_equiv {A B : Type} (e : A ≃ B)
    (F : Set A → A → Prop) (G : Set B → B → Prop)
    (h : ∀ R x, F (e ⁻¹' R) x ↔ G R (e x)) (x : A) :
    (∀ S, (∀ y, F S y → y ∈ S) → x ∈ S) ↔
      ∀ R, (∀ y, G R y → y ∈ R) → e x ∈ R := by
  refine ⟨fun hF R hR => hF (e ⁻¹' R) fun y hy => hR (e y) ((h R y).mp hy), fun hG S hS => ?_⟩
  have hRS : e ⁻¹' (e.symm ⁻¹' S) = S := Set.ext fun _ => by simp
  simpa only [Set.mem_preimage, Equiv.symm_apply_apply] using
    hG (e.symm ⁻¹' S) fun y hy => hS (e.symm y) <|
      hRS ▸ (h (e.symm ⁻¹' S) (e.symm y)).mpr (by simpa using hy)

include hf in
/-- Full-tuple pullback preserves truth for arbitrary scoped relation valuations, including
nested operators. The relation valuations correspond blockwise through `blockEquiv`. -/
theorem realize_onFormula {Γ : List ℕ} {α : Type} (φ : RawFormula L' Γ α) :
    ∀ (ρs : Operator.RelEnv (Γ.map (· * d)) M) (ρt : Operator.RelEnv Γ N),
      (∀ {k} (r : Operator.RelVar Γ k) xs,
        xs ∈ ρs (r.scale d) ↔ blockEquiv e k xs ∈ ρt r) →
      ∀ v : α × Fin d → M,
        (onFormula f φ).Realize interpretation ρs v ↔
          φ.Realize interpretation ρt (fun a => e (fun i => v (a, i))) := by
  induction φ with
  | ofFO φ => exact fun _ _ _ v => hf φ v
  | rel r args => exact fun ρs ρt hρ v => realize_applyTerms_rel f e hf _ _ r args ρs ρt (hρ r) v
  | neg _ ih => exact fun ρs ρt hρ v => not_congr (ih ρs ρt hρ v)
  | conj _ _ ihφ ihψ => exact fun ρs ρt hρ v => and_congr (ihφ ρs ρt hρ v) (ihψ ρs ρt hρ v)
  | ex _ ih => exact fun ρs ρt hρ v => realize_exBlock e _ _ ρs v _ (ih ρs ρt hρ)
  | @op Γ' α' k body args ih =>
    intro ρs ρt hρ v
    let vt : α' → N := fun a => e (fun i => v (a, i))
    let ea := blockEquiv e k
    let xs := ea.symm (fun i => (args i).realize vt)
    let b : RawFormula L ((k * d) :: Γ'.map (· * d))
        (((α' × Fin d) ⊕ Fin (k * d)) ⊕ Fin (k * d)) :=
      ((onFormula f (body 0)).relabel scopeMap).relabel (Sum.map Sum.inl id)
    change (applyTerms f args (lfp b (fun i => .var (.inr i)))).Realize
      interpretation ρs v ↔ (lfp (body 0) args).Realize interpretation ρt vt
    rw [realize_applyTerms f e hf, realize_lfp_prefixed, realize_lfp_prefixed]
    change (∀ S, (∀ ys, b.Realize interpretation (Operator.RelEnv.cons S ρs)
      (Sum.elim (Sum.elim v xs) ys) → ys ∈ S) → xs ∈ S) ↔
      ∀ R, (∀ ys, (body 0).Realize interpretation (Operator.RelEnv.cons R ρt)
        (Sum.elim vt ys) → ys ∈ R) → (fun i => (args i).realize vt) ∈ R
    simpa only [xs, Equiv.apply_symm_apply] using prefixed_equiv ea
      (fun S ys => b.Realize interpretation (Operator.RelEnv.cons S ρs)
        (Sum.elim (Sum.elim v xs) ys))
      (fun R ys => (body 0).Realize interpretation (Operator.RelEnv.cons R ρt)
        (Sum.elim vt ys)) (fun R ys => by
        simp only [b, Operator.Formula.realize_relabel]
        rw [ih 0 (Operator.RelEnv.cons (ea ⁻¹' R) ρs) (Operator.RelEnv.cons R ρt)
          fun {_} r zs => by cases r with | here => rfl | there r => exact hρ r zs]
        exact iff_of_eq (congrArg _ (funext fun a => by cases a <;> rfl))) xs

end Cslib.Logic.FO.LFP.Tuple
