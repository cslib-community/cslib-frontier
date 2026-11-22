/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Logics.Propositional.Defs
public import CslibFrontier.Logics.Propositional.LineProof
public import CslibFrontier.Logics.Propositional.Semantics
public import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

/-!
# Frege proofs

A *Frege system* [Cook and Reckhow][CookReckhow1979] is a line-based propositional proof system
given by finitely many sound axiom schemes and inference rules that are implicationally complete:
whenever `Γ` semantically implies `φ`, there is a proof of `φ` from `Γ`. This file fixes the
Hilbert-style system with the axiom schemes K, S and double-negation elimination for `→` and `⊥`,
the usual introduction and elimination schemes for `∧` and `∨`, and modus ponens as the only rule
(`Cslib.Logic.PL.Frege.IsAxiom`). A *proof* from hypotheses `Γ` is a list of formulas, each a
hypothesis, an axiom instance, or obtained by modus ponens from two earlier lines
(`Cslib.Logic.PL.Frege.IsProof`). Implicational completeness of this system is standard (the
schemes form a classical axiomatization of `→`, `⊥`, `∧` and `∨`) but not yet formalized
([#3069](https://github.com/cslib-community/cslib-frontier/issues/3069)). As in
`CslibFrontier.Logics.Propositional.Resolution.Proof`, proofs are listed from their last line to
their
first, and the size of a proof is its number of lines.

Formulas are cslib's propositions `Cslib.Logic.PL.Proposition` over the atoms `V`, with cslib's
`⊥` (the constructor `Proposition.falsum`) as falsity and cslib's `Proposition.neg φ = φ → ⊥` as
negation. Their Boolean semantics is `Cslib.Logic.PL.Proposition.eval` at `Bool`. No other
formula type of the library fits: the CNF and QBF types have no implication, and circuit formulas
are indexed by a fixed number of inputs.

The file proves soundness (`Cslib.Logic.PL.Frege.IsProof.eval`) and the tools used to build proofs
with explicit line counts:

* `Cslib.Logic.PL.Frege.IsProof.cut`: a proof from `Γ ++ Δ` replays on top of a proof from `Γ`
  among whose lines are the formulas of `Δ`, with at most as many new lines. This lets a later
  step reuse earlier lines, so that simulated proofs keep their line structure.
* `Cslib.Logic.PL.Frege.IsProof.deduction`: the **deduction theorem with linear overhead**. A proof
  from `Γ ++ Δ` becomes a proof from `Γ` containing `Δ ⇒ φ` (`Cslib.Logic.PL.Frege.Formula.imps`)
  for each of its lines `φ`, with at most `10 (|Δ| + 1)` lines per original line. Discharging the
  hypotheses of `Δ` one at a time would instead multiply the size by a constant per hypothesis.

## Main definitions

* `Cslib.Logic.PL.Frege.Formula`.
* `Cslib.Logic.PL.Frege.IsAxiom`, `Cslib.Logic.PL.Frege.rules`,
  `Cslib.Logic.PL.Frege.IsProof`: the Frege system.
* `Cslib.Logic.PL.Frege.DerivableInSize`: derivability in a bounded number of lines.

## Main results

* `Cslib.Logic.PL.Frege.isProof_iff_lineProof`: Frege proofs as `Cslib.Logic.PL.LineProof`
  derivations.
* `Cslib.Logic.PL.Frege.IsProof.eval`: soundness.
* `Cslib.Logic.PL.Frege.IsProof.cut`, `Cslib.Logic.PL.Frege.IsProof.deduction`.

## References

* [S. A. Cook, R. A. Reckhow, *The relative efficiency of propositional proof
  systems*][CookReckhow1979]
-/

public section

namespace Cslib.Logic.PL.Frege

variable {V : Type*}

/-- Formulas: cslib's propositions over the atoms `V`, with `⊥` (`Proposition.falsum`) as
falsity. -/
abbrev Formula (V : Type*) := Proposition V

namespace Formula

/-- A variable. -/
abbrev var (v : V) : Formula V := Proposition.atom v

/-- Implication. -/
abbrev imp (φ ψ : Formula V) : Formula V := Proposition.imp φ ψ

/-- `a₁ → (a₂ → ⋯ → (aₖ → φ))`. -/
@[expose] def imps (Δ : List (Formula V)) (φ : Formula V) : Formula V := Δ.foldr imp φ

@[simp] theorem imps_nil (φ : Formula V) : imps [] φ = φ := rfl
@[simp] theorem imps_cons (a : Formula V) (Δ φ) : imps (a :: Δ) φ = imp a (imps Δ φ) := rfl

end Formula

open Formula

/-- The axiom schemes: K, S, double-negation elimination, and the schemes for `∧` and `∨`. -/
inductive IsAxiom : Formula V → Prop
  /-- `φ → (ψ → φ)`. -/
  | k (φ ψ : Formula V) : IsAxiom (imp φ (imp ψ φ))
  /-- `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | s (φ ψ χ : Formula V) : IsAxiom (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  /-- `¬¬φ → φ`. -/
  | dne (φ : Formula V) : IsAxiom (imp (Proposition.neg (Proposition.neg φ)) φ)
  /-- `φ ∧ ψ → φ`. -/
  | andElimL (φ ψ : Formula V) : IsAxiom (imp (.and φ ψ) φ)
  /-- `φ ∧ ψ → ψ`. -/
  | andElimR (φ ψ : Formula V) : IsAxiom (imp (.and φ ψ) ψ)
  /-- `φ → (ψ → φ ∧ ψ)`. -/
  | andIntro (φ ψ : Formula V) : IsAxiom (imp φ (imp ψ (.and φ ψ)))
  /-- `φ → φ ∨ ψ`. -/
  | orIntroL (φ ψ : Formula V) : IsAxiom (imp φ (.or φ ψ))
  /-- `ψ → φ ∨ ψ`. -/
  | orIntroR (φ ψ : Formula V) : IsAxiom (imp ψ (.or φ ψ))
  /-- `(φ → χ) → ((ψ → χ) → (φ ∨ ψ → χ))`. -/
  | orElim (φ ψ χ : Formula V) : IsAxiom (imp (imp φ χ) (imp (imp ψ χ) (imp (.or φ ψ) χ)))

/-- Frege proofs from hypotheses `Γ`, listed from the last line to the first. -/
inductive IsProof (Γ : List (Formula V)) : List (Formula V) → Prop
  /-- The empty proof. -/
  | nil : IsProof Γ []
  /-- A hypothesis is a new line. -/
  | hyp {L : List (Formula V)} {φ : Formula V} : IsProof Γ L → φ ∈ Γ → IsProof Γ (φ :: L)
  /-- An axiom instance is a new line. -/
  | ax {L : List (Formula V)} {φ : Formula V} : IsProof Γ L → IsAxiom φ → IsProof Γ (φ :: L)
  /-- Modus ponens from two earlier lines `φ` and `φ → ψ`. -/
  | mp {L : List (Formula V)} {φ ψ : Formula V} : IsProof Γ L → φ ∈ L → imp φ ψ ∈ L →
      IsProof Γ (ψ :: L)

/-- Every axiom instance is true under every assignment. -/
theorem IsAxiom.eval {φ : Formula V} (h : IsAxiom φ) (σ : V → Bool) : φ.eval σ = true := by
  cases h <;> simp only [Proposition.eval_imp_bool, Proposition.eval_and_bool,
    Proposition.eval_or_bool, Proposition.eval_bot_bool] <;>
    grind

/-- The rules of the Frege system as `Cslib.Logic.PL.LineRule`s: axiom instances (with no premises)
and modus ponens. -/
@[expose] def rules (V : Type*) : Set (LineRule (Formula V)) :=
  {r | (r.premises = [] ∧ IsAxiom r.concl) ∨ ∃ φ ψ, r = ⟨[φ, imp φ ψ], ψ⟩}

/-- Every Frege rule preserves truth under any assignment. -/
theorem rules_sound {r : LineRule (Formula V)} (hr : r ∈ rules V) {σ : V → Bool}
    (hp : ∀ φ ∈ r.premises, φ.eval σ = true) : r.concl.eval σ = true := by
  rcases hr with ⟨-, hax⟩ | ⟨φ, ψ, rfl⟩
  · exact hax.eval σ
  · have e₁ := hp φ (by simp)
    have e₂ := hp (imp φ ψ) (by simp)
    simp only [Proposition.eval_imp_bool, e₁, Bool.not_true, Bool.false_or] at e₂
    exact e₂

/-- **Frege proofs as `LineProof` derivations.** -/
theorem isProof_iff_lineProof {Γ L : List (Formula V)} :
    IsProof Γ L ↔ LineProof (rules V) {φ | φ ∈ Γ} L := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | hyp _ hφ ih => exact ih.hyp hφ
    | @ax _ φ _ hφ ih => exact ih.step (r := ⟨[], φ⟩) (Or.inl ⟨rfl, hφ⟩) (by simp)
    | @mp _ φ ψ _ h₁ h₂ ih =>
      exact ih.step (r := ⟨[φ, imp φ ψ], ψ⟩) (Or.inr ⟨φ, ψ, rfl⟩) (by simp [h₁, h₂])
  · intro h
    induction h with
    | nil => exact .nil
    | hyp _ hφ ih => exact ih.hyp hφ
    | step _ hr hp ih =>
      rcases hr with ⟨-, hax⟩ | ⟨φ, ψ, rfl⟩
      · exact ih.ax hax
      · exact ih.mp (hp φ (by simp)) (hp (imp φ ψ) (by simp))

/-- **Soundness**: under an assignment satisfying every hypothesis, every line is true. -/
theorem IsProof.eval {Γ L : List (Formula V)} (h : IsProof Γ L) {σ : V → Bool}
    (hσ : ∀ γ ∈ Γ, γ.eval σ = true) : ∀ φ ∈ L, φ.eval σ = true :=
  (isProof_iff_lineProof.1 h).holds hσ fun _ hr => rules_sound hr

/-- `L'` extends the proof `L` by at most `n` lines. -/
abbrev Grows (Γ L L' : List (Formula V)) (n : ℕ) : Prop :=
  LineProof.Grows (rules V) {φ | φ ∈ Γ} L L' n

/-- No new lines. -/
theorem Grows.refl {Γ L : List (Formula V)} (h : IsProof Γ L) : Grows Γ L L 0 :=
  LineProof.Grows.refl (isProof_iff_lineProof.1 h)

/-- The extended list is a proof. -/
theorem Grows.proof {Γ L L' : List (Formula V)} {n : ℕ} (h : Grows Γ L L' n) :
    IsProof Γ L' :=
  isProof_iff_lineProof.2 h.lineProof

/-- Adding an axiom instance. -/
theorem grows_ax {Γ L : List (Formula V)} (h : IsProof Γ L) {φ : Formula V} (hφ : IsAxiom φ) :
    Grows Γ L (φ :: L) 1 :=
  LineProof.Grows.step (r := ⟨[], φ⟩) (isProof_iff_lineProof.1 h) (Or.inl ⟨rfl, hφ⟩) (by simp)

/-- Adding a hypothesis. -/
theorem grows_hyp {Γ L : List (Formula V)} (h : IsProof Γ L) {φ : Formula V} (hφ : φ ∈ Γ) :
    Grows Γ L (φ :: L) 1 :=
  LineProof.Grows.hyp (isProof_iff_lineProof.1 h) hφ

/-- Adding a modus ponens line. -/
theorem grows_mp {Γ L : List (Formula V)} (h : IsProof Γ L) {φ ψ : Formula V} (h₁ : φ ∈ L)
    (h₂ : imp φ ψ ∈ L) : Grows Γ L (ψ :: L) 1 :=
  LineProof.Grows.step (r := ⟨[φ, imp φ ψ], ψ⟩) (isProof_iff_lineProof.1 h)
    (Or.inr ⟨φ, ψ, rfl⟩) (by simp [h₁, h₂])

/-- **Cut**: a proof from `Γ ++ Δ` replays on top of a proof `L` from `Γ` containing every
formula of `Δ`, with at most as many new lines. -/
theorem IsProof.cut {Γ Δ M L : List (Formula V)} (hM : IsProof (Γ ++ Δ) M) (hL : IsProof Γ L)
    (hΔ : ∀ δ ∈ Δ, δ ∈ L) :
    ∃ M', IsProof Γ (M' ++ L) ∧ M'.length ≤ M.length ∧ ∀ φ ∈ M, φ ∈ M' ++ L := by
  obtain ⟨M', hM', hmem, hsub, -, -⟩ := (isProof_iff_lineProof.1 hM).comp
    (isProof_iff_lineProof.1 hL) fun x hx => (List.mem_append.1 hx).imp_right (hΔ x)
  exact ⟨M', isProof_iff_lineProof.2 hM', hsub.length_le, hmem⟩

/-- Proofs are monotone in the hypotheses. -/
theorem IsProof.mono {Γ Γ' L : List (Formula V)} (h : IsProof Γ L) (hΓ : Γ ⊆ Γ') :
    IsProof Γ' L :=
  isProof_iff_lineProof.2 ((isProof_iff_lineProof.1 h).mono_hyp fun _ hx => hΓ hx)

/-- `φ` is derivable from `Γ` in at most `n` lines. -/
@[expose] def DerivableInSize (Γ : List (Formula V)) (φ : Formula V) (n : ℕ) : Prop :=
  ∃ L, IsProof Γ L ∧ φ ∈ L ∧ L.length ≤ n

/-- Two proofs from the same hypotheses can be stacked. -/
theorem IsProof.append {Γ L M : List (Formula V)} (hL : IsProof Γ L) (hM : IsProof Γ M) :
    IsProof Γ (M ++ L) :=
  isProof_iff_lineProof.2 ((isProof_iff_lineProof.1 hM).append (isProof_iff_lineProof.1 hL))

namespace DerivableInSize

variable {Γ : List (Formula V)}

/-- Derivability in `n` lines implies derivability in `m ≥ n` lines. -/
theorem mono {n m : ℕ} {φ : Formula V} (h : DerivableInSize Γ φ n) (hnm : n ≤ m) :
    DerivableInSize Γ φ m := by
  obtain ⟨L, hL, hφ, hlen⟩ := h
  exact ⟨L, hL, hφ, hlen.trans hnm⟩

/-- An axiom instance in one line. -/
theorem ax {φ : Formula V} (h : IsAxiom φ) : DerivableInSize Γ φ 1 :=
  ⟨[φ], IsProof.nil.ax h, List.mem_cons_self, le_rfl⟩

/-- A hypothesis in one line. -/
theorem hyp {φ : Formula V} (h : φ ∈ Γ) : DerivableInSize Γ φ 1 :=
  ⟨[φ], IsProof.nil.hyp h, List.mem_cons_self, le_rfl⟩

/-- Modus ponens, stacking the two derivations. -/
theorem mp {m n : ℕ} {φ ψ : Formula V} (h₁ : DerivableInSize Γ (imp φ ψ) m)
    (h₂ : DerivableInSize Γ φ n) : DerivableInSize Γ ψ (m + n + 1) := by
  obtain ⟨L₁, hL₁, hφψ, hlen₁⟩ := h₁
  obtain ⟨L₂, hL₂, hφ, hlen₂⟩ := h₂
  refine ⟨ψ :: (L₂ ++ L₁), (hL₁.append hL₂).mp (List.mem_append_left _ hφ)
    (List.mem_append_right _ hφψ), List.mem_cons_self, by simp; omega⟩

/-- `φ → φ` in five lines. -/
theorem id (φ : Formula V) : DerivableInSize Γ (imp φ φ) 5 :=
  (((ax (IsAxiom.s φ (imp φ φ) φ)).mp (ax (IsAxiom.k φ (imp φ φ)))).mp
    (ax (IsAxiom.k φ φ))).mono (by omega)

/-- Weakening under an antecedent `a`. -/
theorem lift {n : ℕ} {φ : Formula V} (a : Formula V) (h : DerivableInSize Γ φ n) :
    DerivableInSize Γ (imp a φ) (n + 2) :=
  ((ax (IsAxiom.k φ a)).mp h).mono (by omega)

/-- Hypothetical syllogism. -/
theorem trans {m n : ℕ} {P Q R : Formula V} (h₁ : DerivableInSize Γ (imp P Q) m)
    (h₂ : DerivableInSize Γ (imp Q R) n) : DerivableInSize Γ (imp P R) (m + n + 5) :=
  (((ax (IsAxiom.s P Q R)).mp (h₂.lift P)).mp h₁).mono (by omega)

/-- `a → (b₁ → ⋯ → bₖ → a)`. -/
theorem imp_imps_self (a : Formula V) (Δ : List (Formula V)) :
    DerivableInSize Γ (imp a (imps Δ a)) (5 + 6 * Δ.length) := by
  induction Δ with
  | nil => exact id a
  | cons b Δ ih =>
    have h := ((ax (IsAxiom.s a (imps Δ a) (imp b (imps Δ a)))).mp
      ((ax (IsAxiom.k (imps Δ a) b)).lift a)).mp ih
    exact h.mono (by simp; omega)

/-- `b₁ → ⋯ → bₖ → a` for `a` among the `bᵢ`. -/
theorem imps_mem {a : Formula V} {Δ : List (Formula V)} (h : a ∈ Δ) :
    DerivableInSize Γ (imps Δ a) (5 + 8 * Δ.length) := by
  induction Δ with
  | nil => simp at h
  | cons b Δ ih =>
    by_cases hab : a = b
    · subst hab
      exact (imp_imps_self a Δ).mono (by simp; omega)
    · have h' : a ∈ Δ := (List.mem_cons.1 h).resolve_left hab
      exact ((ih h').lift b).mono (by simp; omega)

/-- Distribution of `b₁ → ⋯ → bₖ →` over implication. -/
theorem imps_dist (Δ : List (Formula V)) (φ ψ : Formula V) :
    DerivableInSize Γ (imp (imps Δ (imp φ ψ)) (imp (imps Δ φ) (imps Δ ψ)))
      (5 + 10 * Δ.length) := by
  induction Δ with
  | nil => exact id _
  | cons a Δ ih =>
    have h₁ := (ax (IsAxiom.s a (imps Δ (imp φ ψ)) (imp (imps Δ φ) (imps Δ ψ)))).mp (ih.lift a)
    have h := h₁.trans (ax (IsAxiom.s a (imps Δ φ) (imps Δ ψ)))
    exact h.mono (by simp; omega)

end DerivableInSize

/-- Appending a derivation from the same hypotheses. -/
theorem Grows.of_derivableInSize {Γ L : List (Formula V)} (hL : IsProof Γ L) {n : ℕ}
    {φ : Formula V} (h : DerivableInSize Γ φ n) : ∃ L', Grows Γ L L' n ∧ φ ∈ L' := by
  obtain ⟨M, hM, hφ, hlen⟩ := h
  exact ⟨M ++ L, LineProof.Grows.of_append (isProof_iff_lineProof.1 (hL.append hM)) hlen,
    List.mem_append_left _ hφ⟩

/-- Weakening an available line under the antecedents `Δ`, two lines per antecedent. -/
theorem Grows.imps_of_mem {Γ L : List (Formula V)} (hL : IsProof Γ L) {φ : Formula V}
    (hφ : φ ∈ L) (Δ : List (Formula V)) :
    ∃ L', Grows Γ L L' (2 * Δ.length) ∧ imps Δ φ ∈ L' := by
  induction Δ with
  | nil => exact ⟨L, Grows.refl hL, hφ⟩
  | cons a Δ ih =>
    obtain ⟨L₁, g₁, h₁⟩ := ih
    have g₂ := grows_ax g₁.proof (IsAxiom.k (imps Δ φ) a)
    have g₃ := grows_mp g₂.proof (List.mem_cons_of_mem _ h₁) List.mem_cons_self
    exact ⟨_, (g₁.trans g₂).trans g₃ |>.mono (by simp; omega), List.mem_cons_self⟩

/-- **Deduction theorem with linear overhead**: a proof from `Γ ++ Δ` becomes a proof from `Γ` of
`Δ ⇒ φ` for each of its lines `φ`, with at most `10 (|Δ| + 1)` lines per original line. -/
theorem IsProof.deduction {Γ Δ M : List (Formula V)} (hM : IsProof (Γ ++ Δ) M)
    {L : List (Formula V)} (hL : IsProof Γ L) :
    ∃ L', Grows Γ L L' (10 * (Δ.length + 1) * M.length) ∧ ∀ φ ∈ M, imps Δ φ ∈ L' :=
  LineProof.Grows.simulate (imps Δ) (10 * (Δ.length + 1))
    (isProof_iff_lineProof.1 hM) (isProof_iff_lineProof.1 hL)
    (fun h' φ hφ _ => by
      rcases List.mem_append.1 hφ with hφ | hφ
      · have g₂ := grows_hyp (isProof_iff_lineProof.2 h') hφ
        obtain ⟨L₃, g₃, h₃⟩ := Grows.imps_of_mem g₂.proof List.mem_cons_self Δ
        exact ⟨L₃, (g₂.trans g₃).mono (by omega), h₃⟩
      · obtain ⟨L₂, g₂, h₂⟩ := Grows.of_derivableInSize (isProof_iff_lineProof.2 h')
          (DerivableInSize.imps_mem (Γ := Γ) hφ)
        exact ⟨L₂, g₂.mono (by omega), h₂⟩)
    fun h' r hr _ hp => by
      rcases hr with ⟨-, hax⟩ | ⟨φ, ψ, rfl⟩
      · have g₂ := grows_ax (isProof_iff_lineProof.2 h') hax
        obtain ⟨L₃, g₃, h₃⟩ := Grows.imps_of_mem g₂.proof List.mem_cons_self Δ
        exact ⟨L₃, (g₂.trans g₃).mono (by omega), h₃⟩
      · obtain ⟨L₂, g₂, h₂⟩ := Grows.of_derivableInSize (isProof_iff_lineProof.2 h')
          (DerivableInSize.imps_dist (Γ := Γ) Δ φ ψ)
        have hφ := (hp φ (by simp)).2
        have hφψ := (hp (imp φ ψ) (by simp)).2
        have g₃ := grows_mp g₂.proof (g₂.subset hφψ) h₂
        have g₄ := grows_mp g₃.proof (List.mem_cons_of_mem _ (g₂.subset hφ)) List.mem_cons_self
        exact ⟨_, ((g₂.trans g₃).trans g₄).mono (by omega), List.mem_cons_self⟩

/-- Detaching the antecedents `Δ` of an available line `Δ ⇒ φ`, one line per antecedent, when
every antecedent is available. -/
theorem Grows.imps_elim {Γ L : List (Formula V)} (hL : IsProof Γ L) {Δ : List (Formula V)}
    {φ : Formula V} (h : imps Δ φ ∈ L) (hΔ : ∀ δ ∈ Δ, δ ∈ L) :
    ∃ L', Grows Γ L L' Δ.length ∧ φ ∈ L' := by
  induction Δ generalizing L with
  | nil => exact ⟨L, Grows.refl hL, h⟩
  | cons a Δ ih =>
    have g₁ := grows_mp hL (hΔ a List.mem_cons_self) h
    obtain ⟨L₂, g₂, h₂⟩ := ih g₁.proof List.mem_cons_self
      fun δ hδ => List.mem_cons_of_mem _ (hΔ δ (List.mem_cons_of_mem _ hδ))
    exact ⟨L₂, (g₁.trans g₂).mono (by simp; omega), h₂⟩

/-- Adding hypotheses: every formula of `Δ` that is a hypothesis or already available becomes
available, one line per formula. -/
theorem Grows.collect {Γ L : List (Formula V)} (hL : IsProof Γ L) {Δ : List (Formula V)}
    (hΔ : ∀ δ ∈ Δ, δ ∈ Γ ∨ δ ∈ L) : ∃ L', Grows Γ L L' Δ.length ∧ ∀ δ ∈ Δ, δ ∈ L' :=
  LineProof.Grows.collect (isProof_iff_lineProof.1 hL) hΔ

end Cslib.Logic.PL.Frege
