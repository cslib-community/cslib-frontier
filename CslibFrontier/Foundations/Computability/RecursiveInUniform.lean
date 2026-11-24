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
where a primitive recursive test asks for it, and otherwise returns its input.

## Main definitions

* `Nat.RecursiveIn.Code.HasUniformCode`: one code computes a family relative to a family of
  oracles.

## Main results

* `Nat.RecursiveIn.Code.HasUniformCode.of_partrec`, `.oracle`, `.pair`, `.comp`, `.prec`,
  `.rfind`: closure under the constructors of `Nat.RecursiveIn`.
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

/-- A guarded call: where the primitive recursive test `b` is `0` the input is returned and `F` is
not run, so its divergence there does not matter. -/
theorem ite {b : ℕ → ℕ} (hb : Nat.Primrec b) {F : ι → ℕ →. ℕ} (hF : HasUniformCode o F) :
    HasUniformCode o fun i n => if b n = 0 then Part.some n else F i n := by
  have hflag : Nat.Primrec fun n => Nat.pair n (if b n = 0 then 0 else 1) := by
    refine Nat.Primrec.pair Nat.Primrec.id ?_
    have : _root_.Primrec fun n => if b n = 0 then 0 else 1 :=
      _root_.Primrec.ite (_root_.Primrec.eq.comp (_root_.Primrec.nat_iff.2 hb)
        (_root_.Primrec.const 0)) (_root_.Primrec.const 0) (_root_.Primrec.const 1)
    exact _root_.Primrec.nat_iff.1 this
  refine ((HasUniformCode.prec (of_primrec Nat.Primrec.id)
    (hF.comp (of_primrec Nat.Primrec.left))).comp (of_primrec hflag)).of_eq fun i n => ?_
  by_cases h : b n = 0 <;>
    simp only [h, ↓reduceIte, ← Part.pure_eq_some, pure_bind, Nat.unpaired, Nat.unpair_pair]
  · rfl
  · change (pure n >>= fun _ => pure n >>= F i) = F i n
    simp only [pure_bind]
    exact Part.bind_some _ _

theorem recursiveIn {F : ι → ℕ →. ℕ} (hF : HasUniformCode o F) (i : ι) :
    Nat.RecursiveIn {o i} (F i) := by
  obtain ⟨c, hc⟩ := hF
  exact exists_code.mpr ⟨c, hc i⟩

end HasUniformCode

end Nat.RecursiveIn.Code
