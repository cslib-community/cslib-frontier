/-
Copyright (c) 2026 Christian Reitwiessner, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Matthew Doty
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/RecursiveIn.lean`)

public import CslibFrontier.Foundations.Computability.RecursiveInCode

/-!
# Oracle-uniform codes

`Nat.RecursiveIn.Code.exists_code` gives, for each oracle `g`, some code computing a function
relative to `g`; the code may depend on `g`. Simulations of oracle machines and oracle programs
produce one code that works for every oracle. `Code.HasUniformCode o F` states this for a family
of oracles `o : ι → ℕ →. ℕ`: a single code computes `F i` relative to `o i` for every index `i`.
The family is arbitrary, so both partial oracles (`o := id`) and Boolean membership oracles are
instances.

The predicate is closed under the constructors of `Nat.RecursiveIn`, and contains every partial
recursive function. `HasUniformCode.ite` adds a guarded call: it runs a partial computation only
where a computable test asks for it, and otherwise returns its input.

## Main definitions

* `Nat.RecursiveIn.Code.HasUniformCode`: one code computes a family relative to a family of
  oracles.

## Main results

* `Nat.RecursiveIn.Code.HasUniformCode.of_partrec`, `.of_computable`, `.oracle`, `.pair`,
  `.comp`, `.prec`, `.rfind`: closure under the constructors of `Nat.RecursiveIn`.
* `Nat.RecursiveIn.Code.HasUniformCode.ite`: a guarded call.
* `Nat.RecursiveIn.Code.HasUniformCode.recursiveIn`: each member is recursive in its oracle.
-/

@[expose] public section

namespace Nat.RecursiveIn.Code

variable {ι : Type*} {o : ι → ℕ →. ℕ}

/-- One code computes `F i` relative to the oracle `o i`, for every index `i`. -/
def HasUniformCode (o : ι → ℕ →. ℕ) (F : ι → ℕ →. ℕ) : Prop :=
  ∃ c : Code, ∀ i, c.eval (o i) = F i

namespace HasUniformCode

theorem of_partrec {f : ℕ →. ℕ} (hf : Nat.Partrec f) : HasUniformCode o fun _ => f := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  exact ⟨ofPartrec c, fun _ => (eval_ofPartrec _ _).trans hc⟩

theorem of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    HasUniformCode o fun _ n => Part.some (f n) :=
  of_partrec (Nat.Partrec.of_primrec hf)

theorem oracle : HasUniformCode o o :=
  ⟨Code.oracle, fun _ => rfl⟩

theorem comp {F G : ι → ℕ →. ℕ} (hF : HasUniformCode o F) (hG : HasUniformCode o G) :
    HasUniformCode o fun i n => G i n >>= F i := by
  obtain ⟨cf, hcf⟩ := hF
  obtain ⟨cg, hcg⟩ := hG
  exact ⟨Code.comp cf cg, fun i => by rw [eval, hcf, hcg]⟩

theorem pair {F G : ι → ℕ →. ℕ} (hF : HasUniformCode o F) (hG : HasUniformCode o G) :
    HasUniformCode o fun i n => Nat.pair <$> F i n <*> G i n := by
  obtain ⟨cf, hcf⟩ := hF
  obtain ⟨cg, hcg⟩ := hG
  exact ⟨Code.pair cf cg, fun i => by rw [eval, hcf, hcg]⟩

theorem prec {F G : ι → ℕ →. ℕ} (hF : HasUniformCode o F) (hG : HasUniformCode o G) :
    HasUniformCode o fun i => Nat.unpaired fun a n =>
      n.rec (F i a) fun y ih => ih >>= fun x => G i (Nat.pair a (Nat.pair y x)) := by
  obtain ⟨cf, hcf⟩ := hF
  obtain ⟨cg, hcg⟩ := hG
  exact ⟨Code.prec cf cg, fun i => by rw [eval, hcf, hcg]⟩

theorem rfind {F : ι → ℕ →. ℕ} (hF : HasUniformCode o F) :
    HasUniformCode o fun i a =>
      Nat.rfind fun n => (fun m => m = 0) <$> F i (Nat.pair a n) := by
  obtain ⟨c, hc⟩ := hF
  exact ⟨Code.rfind c, fun i => funext fun a => by rw [eval_rfind, hc]⟩

theorem of_eq {F G : ι → ℕ →. ℕ} (hF : HasUniformCode o F) (h : ∀ i n, F i n = G i n) :
    HasUniformCode o G := by
  obtain ⟨c, hc⟩ := hF
  exact ⟨c, fun i => (hc i).trans (funext (h i))⟩

/-- A total computable function, used by the same code for every oracle. -/
theorem of_computable {f : ℕ → ℕ} (hf : Computable f) :
    HasUniformCode o fun _ n => Part.some (f n) :=
  of_partrec (Partrec.nat_iff.1 hf)

/-- A guarded call: where the computable test `b` is `0` the input is returned and `F` is not
run, so its divergence there does not matter. -/
theorem ite {b : ℕ → ℕ} (hb : Computable b) {F : ι → ℕ →. ℕ} (hF : HasUniformCode o F) :
    HasUniformCode o fun i n => if b n = 0 then Part.some n else F i n := by
  have hflag : Computable fun n => Nat.pair n (min (b n) 1) :=
    (Primrec₂.to_comp Primrec₂.natPair).comp Computable.id
      ((Primrec₂.to_comp _root_.Primrec.nat_min).comp hb (Computable.const 1))
  refine ((HasUniformCode.prec (of_primrec Nat.Primrec.id)
    (hF.comp (of_primrec Nat.Primrec.left))).comp (of_computable hflag)).of_eq fun i n => ?_
  rcases Nat.eq_zero_or_pos (b n) with h | h
  · simp only [h, ↓reduceIte, ← Part.pure_eq_some, pure_bind, Nat.unpaired, Nat.unpair_pair]
    rfl
  · simp only [h.ne', ↓reduceIte, Nat.min_eq_right h, ← Part.pure_eq_some, pure_bind,
      Nat.unpaired, Nat.unpair_pair]
    change (pure n >>= fun _ => pure n >>= F i) = F i n
    simp only [pure_bind]
    exact Part.bind_some _ _

theorem recursiveIn {F : ι → ℕ →. ℕ} (hF : HasUniformCode o F) (i : ι) :
    Nat.RecursiveIn {o i} (F i) := by
  obtain ⟨c, hc⟩ := hF
  exact exists_code.mpr ⟨c, hc i⟩

end HasUniformCode

end Nat.RecursiveIn.Code
