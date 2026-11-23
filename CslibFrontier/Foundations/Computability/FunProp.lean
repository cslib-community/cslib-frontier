/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/Partrec.lean`)

public import CslibFrontier.Init
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.Primrec.List
public import Mathlib.Tactic.FunProp

/-!
# `fun_prop` for primitive recursive and computable functions

Registers Mathlib's `Primrec` and `Computable` with `fun_prop`. The structural rules (identity,
constants, composition, pairing and projections) are Mathlib's; the operation rules below restate
Mathlib's `Primrec` / `Computable` closure lemmas in compositional form, so that a goal such as
`Primrec fun p : ℕ × ℕ => (p.2 - 1, p.1.unpair.1)` is closed by `fun_prop` instead of by hand-built
`Primrec.fst.comp (Primrec.snd.comp …)` trees. `Primrec.to_comp` is registered as the transition
from `Primrec` to `Computable`.

## Main results

* `Primrec.nat_add'`, `Primrec.nat_sub'`, `Primrec.unpair'`, `Primrec.natPair'`,
  `Primrec.option_getD'`, `Primrec.list_getElem?'`, …: compositional `Primrec` rules.
* `Computable.unpair'`, `Computable.succ'`, `Computable.natPair'`, …: compositional `Computable`
  rules.
-/

public section

attribute [fun_prop] Primrec Computable

variable {α β γ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

namespace Primrec

attribute [fun_prop] Primrec.id Primrec.const Primrec.to_comp

/-- Composition, in the form `fun_prop` expects. -/
@[fun_prop]
theorem comp' {f : β → γ} {g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => f (g a) :=
  hf.comp hg

@[fun_prop]
theorem pair' {f : α → β} {g : α → γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => (f a, g a) :=
  hf.pair hg

@[fun_prop]
theorem fst' {f : α → β × γ} (hf : Primrec f) : Primrec fun a => (f a).1 :=
  Primrec.fst.comp hf

@[fun_prop]
theorem snd' {f : α → β × γ} (hf : Primrec f) : Primrec fun a => (f a).2 :=
  Primrec.snd.comp hf

@[fun_prop]
theorem succ' {f : α → ℕ} (hf : Primrec f) : Primrec fun a => (f a).succ :=
  Primrec.succ.comp hf

@[fun_prop]
theorem nat_add' {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => f a + g a :=
  Primrec.nat_add.comp hf hg

@[fun_prop]
theorem nat_sub' {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => f a - g a :=
  Primrec.nat_sub.comp hf hg

@[fun_prop]
theorem nat_mul' {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => f a * g a :=
  Primrec.nat_mul.comp hf hg

@[fun_prop]
theorem unpair' {f : α → ℕ} (hf : Primrec f) : Primrec fun a => (f a).unpair :=
  Primrec.unpair.comp hf

@[fun_prop]
theorem natPair' {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => Nat.pair (f a) (g a) :=
  Primrec₂.natPair.comp hf hg

@[fun_prop]
theorem encode' {f : α → β} (hf : Primrec f) : Primrec fun a => Encodable.encode (f a) :=
  Primrec.encode.comp hf

@[fun_prop]
theorem ofNat' (β : Type*) [Denumerable β] {f : α → ℕ} (hf : Primrec f) :
    Primrec fun a => Denumerable.ofNat β (f a) :=
  (Primrec.ofNat β).comp hf

@[fun_prop]
theorem option_some' {f : α → β} (hf : Primrec f) : Primrec fun a => some (f a) :=
  Primrec.option_some.comp hf

@[fun_prop]
theorem option_getD' {f : α → Option β} {g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => (f a).getD (g a) :=
  Primrec.option_getD.comp hf hg

@[fun_prop]
theorem option_bind' {f : α → Option β} {g : α → β → Option σ} (hf : Primrec f)
    (hg : Primrec fun p : α × β => g p.1 p.2) : Primrec fun a => (f a).bind (g a) :=
  Primrec.option_bind hf hg

@[fun_prop]
theorem list_getElem?' {f : α → List β} {n : α → ℕ} (hf : Primrec f) (hn : Primrec n) :
    Primrec fun a => (f a)[n a]? :=
  Primrec.list_getElem?.comp hf hn

@[fun_prop]
theorem list_length' {f : α → List β} (hf : Primrec f) : Primrec fun a => (f a).length :=
  Primrec.list_length.comp hf

@[fun_prop]
theorem cond' {c : α → Bool} {f g : α → σ} (hc : Primrec c) (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => bif c a then f a else g a :=
  Primrec.cond hc hf hg

@[fun_prop]
theorem nat_bodd' {f : α → ℕ} (hf : Primrec f) : Primrec fun a => (f a).bodd :=
  Primrec.nat_bodd.comp hf

@[fun_prop]
theorem nat_div2' {f : α → ℕ} (hf : Primrec f) : Primrec fun a => (f a).div2 :=
  Primrec.nat_div2.comp hf

@[fun_prop]
theorem list_range' {f : α → ℕ} (hf : Primrec f) : Primrec fun a => List.range (f a) :=
  Primrec.list_range.comp hf

@[fun_prop]
theorem list_map' {f : α → List β} {g : α → β → σ} (hf : Primrec f)
    (hg : Primrec fun p : α × β => g p.1 p.2) : Primrec fun a => (f a).map (g a) :=
  Primrec.list_map hf hg

@[fun_prop]
theorem option_map' {f : α → Option β} {g : α → β → σ} (hf : Primrec f)
    (hg : Primrec fun p : α × β => g p.1 p.2) : Primrec fun a => (f a).map (g a) :=
  Primrec.option_map hf hg

/-- `do`-notation binds in `Option`. -/
@[fun_prop]
theorem option_bind_bind {β σ : Type} [Primcodable β] [Primcodable σ] {f : α → Option β}
    {g : α → β → Option σ} (hf : Primrec f) (hg : Primrec fun p : α × β => g p.1 p.2) :
    Primrec fun a => f a >>= g a :=
  Primrec.option_bind hf hg

@[fun_prop]
theorem nat_casesOn_comp {f : α → ℕ} {g : α → σ} {h : α → ℕ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec fun p : α × ℕ => h p.1 p.2) :
    Primrec fun a => (Nat.casesOn (motive := fun _ => σ) (f a) (g a) (h a) : σ) :=
  Primrec.nat_casesOn hf hg hh

@[fun_prop]
theorem option_casesOn_comp {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Primrec o)
    (hf : Primrec f) (hg : Primrec fun p : α × β => g p.1 p.2) :
    Primrec fun a => (Option.casesOn (motive := fun _ => σ) (o a) (f a) (g a) : σ) :=
  Primrec.option_casesOn ho hf hg

@[fun_prop]
theorem nat_div' {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => f a / g a :=
  Primrec.nat_div.comp hf hg

@[fun_prop]
theorem nat_mod' {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => f a % g a :=
  Primrec.nat_mod.comp hf hg

@[fun_prop]
theorem nat_max' {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => max (f a) (g a) :=
  Primrec.nat_max.comp hf hg

/-- Equality tests, as `Bool`-valued functions. -/
@[fun_prop]
theorem decide_eq' [DecidableEq β] {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => decide (f a = g a) :=
  Primrec.eq.decide.comp hf hg

@[fun_prop]
theorem decide_le' {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => decide (f a ≤ g a) :=
  Primrec.nat_le.decide.comp hf hg

/-- `if` on a condition whose `Bool` indicator is primitive recursive. -/
@[fun_prop]
theorem ite' {c : α → Prop} [DecidablePred c] {f g : α → σ}
    (hc : Primrec fun a => decide (c a)) (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => if c a then f a else g a :=
  Primrec.ite (primrecPred_iff_primrec_decide.2 hc) hf hg

end Primrec

namespace Computable

attribute [fun_prop] Computable.id Computable.const

@[fun_prop]
theorem comp' {f : β → γ} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => f (g a) :=
  hf.comp hg

@[fun_prop]
theorem pair' {f : α → β} {g : α → γ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a, g a) :=
  hf.pair hg

@[fun_prop]
theorem fst' {f : α → β × γ} (hf : Computable f) : Computable fun a => (f a).1 :=
  Computable.fst.comp hf

@[fun_prop]
theorem snd' {f : α → β × γ} (hf : Computable f) : Computable fun a => (f a).2 :=
  Computable.snd.comp hf

@[fun_prop]
theorem succ' {f : α → ℕ} (hf : Computable f) : Computable fun a => (f a).succ :=
  Computable.succ.comp hf

@[fun_prop]
theorem unpair' {f : α → ℕ} (hf : Computable f) : Computable fun a => (f a).unpair :=
  Computable.unpair.comp hf

@[fun_prop]
theorem ofNat' (β : Type*) [Denumerable β] {f : α → ℕ} (hf : Computable f) :
    Computable fun a => Denumerable.ofNat β (f a) :=
  (Computable.ofNat β).comp hf

@[fun_prop]
theorem option_getD' {f : α → Option β} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a).getD (g a) :=
  Computable.option_getD hf hg

@[fun_prop]
theorem nat_add' {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => f a + g a :=
  Primrec.nat_add.to_comp.comp hf hg

@[fun_prop]
theorem nat_sub' {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => f a - g a :=
  Primrec.nat_sub.to_comp.comp hf hg

@[fun_prop]
theorem natPair' {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => Nat.pair (f a) (g a) :=
  Primrec₂.natPair.to_comp.comp hf hg

end Computable
