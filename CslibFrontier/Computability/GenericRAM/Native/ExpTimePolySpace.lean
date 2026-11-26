/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Certificates in factored time and polynomial space

A native certificate runs *in time `K` times a polynomial and in polynomial space*
(`Cslib.GenericRAM.NativeCertificate.FactorTimePolySpace`) when, for constants `C` and `d`, its time
is at most `C K a (n + 1) ^ d` and its space at most `C (n + 1) ^ d` on inputs `a` of encoded
length `n`. Because a polynomial space bound also bounds the encoded intermediate value
(`Cslib.GenericRAM.NativeCertificate.polyBounded_length_of_space`), this shape closes under pairing,
sequential composition, conditional branching and retained-input option elimination, recovering
`Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace` at `K a = 2 ^ E a`.

## Main definitions

* `Cslib.GenericRAM.NativeCertificate.FactorTimePolySpace`,
  `Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace`.

## Main results

* `Cslib.GenericRAM.NativeCertificate.polyBounded_length_of_space`,
  `Cslib.GenericRAM.NativeCertificate.computableInPolySpace`: polynomial output-length and
  polynomial-space bounds from `PolyBounded` certificate workspace.
* `Cslib.GenericRAM.NativeCertificate.FactorTimePolySpace.prod`,
  `Cslib.GenericRAM.NativeCertificate.FactorTimePolySpace.comp`,
  `Cslib.GenericRAM.NativeCertificate.FactorTimePolySpace.branch`,
  `Cslib.GenericRAM.NativeCertificate.FactorTimePolySpace.option`: closure across combinators.
* `Cslib.GenericRAM.NativeCertificate.FactorTimePolySpace.computableInO`,
  `Cslib.GenericRAM.NativeCertificate.FactorTimePolySpace.exists_poly_computableInO`,
  `Cslib.GenericRAM.NativeCertificate.FactorTimePolySpace.computableInPolySpace`: machine bounds.
* `Cslib.GenericRAM.NativeCertificate.expTimePolySpace_ofPolyTime`,
  `Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace.prod`,
  `Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace.comp_ofPolyTime`,
  `Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace.computableInO`,
  `Cslib.GenericRAM.NativeCertificate.branch_bounds_of_two_pow`: `2 ^ E` specializations.
-/

public section

namespace Cslib.GenericRAM.NativeCertificate

open Turing.MultiTapeTM

variable {α β γ : Type} {enc : α ↪ List Bool} {eβ : β ↪ List Bool} {eγ : γ ↪ List Bool}
  {f : α → β} {g : α → γ}

/-- A polynomial space bound on a native certificate also polynomially bounds the encoded output
length. -/
theorem polyBounded_length_of_space {c : NativeCertificate f enc eβ}
    (hs : PolyBounded (fun a => (enc a).length) c.space) :
    PolyBounded (fun a => (enc a).length) (fun a => (eβ (f a)).length) :=
  let ⟨k, _, hl⟩ := c.computes; ((PolyBounded.const k).mul (hs.add (.const 1))).mono hl

/-- A native certificate with polynomially bounded workspace witnesses `ComputableInPolySpace`,
regardless of its running time. -/
theorem computableInPolySpace (c : NativeCertificate f enc eβ)
    (hs : PolyBounded (fun a => (enc a).length) c.space) :
    ComputableInPolySpace f enc eβ := by
  obtain ⟨p, hp, hle⟩ := hs; obtain ⟨k, htm, hl⟩ := c.computes
  have hk (a : α) : k * (c.space a + 1) ≤ k * (p (enc a).length + 1) :=
    Nat.mul_le_mul_left k (Nat.add_le_add_right (hle a) 1)
  exact ⟨_, fun n => k * (p n + 1), (Cslib.PolynomiallyBounded.const k).mul (hp.add (.const 1)),
    htm.mono (fun _ => le_rfl) hk, fun a => (hl a).trans (hk a)⟩

/-- A certificate **runs in time `K` times a polynomial and in polynomial space**: for constants
`C` and `d`, its time is at most `C K a (n + 1) ^ d` and its space at most `C (n + 1) ^ d` on
inputs `a` of encoded length `n`. -/
@[expose] def FactorTimePolySpace (c : NativeCertificate f enc eβ) (K : α → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ a, c.time a ≤ C * K a * ((enc a).length + 1) ^ d ∧
    c.space a ≤ C * ((enc a).length + 1) ^ d

namespace FactorTimePolySpace

variable {c : NativeCertificate f enc eβ} {K K' : α → ℕ}

theorem space_polyBounded (h : c.FactorTimePolySpace K) :
    PolyBounded (fun a => (enc a).length) c.space :=
  let ⟨C, d, h⟩ := h; .of_forall_le C d fun a => (h a).2

theorem exists_time_polyBounded (h : c.FactorTimePolySpace K) :
    ∃ T : α → ℕ, PolyBounded (fun a => (enc a).length) T ∧ ∀ a, c.time a ≤ K a * T a :=
  let ⟨C, d, h⟩ := h
  ⟨fun a => C * ((enc a).length + 1) ^ d, .of_forall_le C d fun _ => le_rfl,
    fun a => (h a).1.trans_eq (by ring)⟩

/-- Package polynomial space and a factored time bound `c.time a ≤ K a * T a` with polynomial
`T`. -/
theorem of_polyBounded {T : α → ℕ} (hT : PolyBounded (fun a => (enc a).length) T)
    (hS : PolyBounded (fun a => (enc a).length) c.space)
    (ht : ∀ a, c.time a ≤ K a * T a) : c.FactorTimePolySpace K := by
  obtain ⟨ct, dt, hleT⟩ := hT.exists_le; obtain ⟨cs, ds, hleS⟩ := hS.exists_le
  refine ⟨ct + cs, dt + ds, fun a => ⟨(ht a).trans ?_, (hleS a).trans ?_⟩⟩
  · have hpow : ((enc a).length + 1) ^ dt ≤ ((enc a).length + 1) ^ (dt + ds) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right _ _)
    have hmul := (hleT a).trans (Nat.mul_le_mul (Nat.le_add_right ct cs) hpow)
    exact (Nat.mul_le_mul_left (K a) hmul).trans_eq (by ring)
  · exact Nat.mul_le_mul (Nat.le_add_left _ _)
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _))

theorem mono_const (h : c.FactorTimePolySpace K) (M : ℕ) (hK : ∀ a, K a ≤ M * K' a) :
    c.FactorTimePolySpace K' := by
  obtain ⟨T, hT, ht⟩ := h.exists_time_polyBounded
  refine of_polyBounded ((PolyBounded.const M).mul hT) h.space_polyBounded fun a => ?_
  exact (ht a).trans ((Nat.mul_le_mul_right (T a) (hK a)).trans_eq (by ring))

theorem mono (h : c.FactorTimePolySpace K) (hK : ∀ a, K a ≤ K' a) : c.FactorTimePolySpace K' :=
  h.mono_const 1 fun a => by simpa only [one_mul] using hK a

/-- A polynomially bounded factor in `M a * K a` is absorbed into the polynomial overhead. -/
theorem absorb_polyBounded {M : α → ℕ} (h : c.FactorTimePolySpace (fun a => M a * K a))
    (hM : PolyBounded (fun a => (enc a).length) M) : c.FactorTimePolySpace K := by
  obtain ⟨T, hT, ht⟩ := h.exists_time_polyBounded
  exact of_polyBounded (hM.mul hT) h.space_polyBounded fun a => (ht a).trans_eq (by ring)

theorem ofIsPolynomial (hc : c.IsPolynomial) : c.FactorTimePolySpace (fun _ => 1) :=
  of_polyBounded hc.1 hc.2 fun _ => by rw [one_mul]

theorem ofPolyTime (hf : ComputableInPolyTime f enc eβ) :
    (NativeCertificate.ofPolyTime hf).FactorTimePolySpace (fun _ => 1) :=
  ofIsPolynomial (ofPolyTime_isPolynomial hf)

theorem congr {f' : α → β} (h : c.FactorTimePolySpace K) (hfg : ∀ a, f a = f' a) :
    (c.congr hfg).FactorTimePolySpace K := h

theorem snd {f : α → β × γ} {c : NativeCertificate f enc (encPair eβ eγ)}
    (h : c.FactorTimePolySpace K) : c.snd.FactorTimePolySpace K := h

/-- **Pairs add the time factors** while retaining polynomial workspace. -/
theorem prod {c' : NativeCertificate g enc eγ} (h : c.FactorTimePolySpace K)
    (h' : c'.FactorTimePolySpace K') :
    (c.prod c').FactorTimePolySpace (fun a => K a + K' a) := by
  obtain ⟨T, hT, ht⟩ := h.exists_time_polyBounded
  obtain ⟨T', hT', ht'⟩ := h'.exists_time_polyBounded
  refine of_polyBounded (hT.add hT') (h.space_polyBounded.add h'.space_polyBounded) fun a => ?_
  rw [prod_time]; have := ht a; have := ht' a; nlinarith

theorem prod_same {c' : NativeCertificate g enc eγ} (h : c.FactorTimePolySpace K)
    (h' : c'.FactorTimePolySpace K) : (c.prod c').FactorTimePolySpace K :=
  (h.prod h').mono_const 2 fun _ => by omega

/-- **Sequential composition** adds the producer's factor and the consumer's factor evaluated at
the intermediate value, whose encoded length is polynomially bounded by the producer's workspace. -/
theorem comp {r : β → γ} {c₂ : NativeCertificate r eβ eγ} {K₂ : β → ℕ}
    (h₁ : c.FactorTimePolySpace K) (h₂ : c₂.FactorTimePolySpace K₂) :
    (c₂.comp c).FactorTimePolySpace (fun a => K a + K₂ (f a)) := by
  have hlen := polyBounded_length_of_space h₁.space_polyBounded
  obtain ⟨T₁, hT₁, ht₁⟩ := h₁.exists_time_polyBounded
  obtain ⟨T₂, hT₂, ht₂⟩ := h₂.exists_time_polyBounded
  refine of_polyBounded (hT₁.add (hT₂.comp hlen))
    (h₁.space_polyBounded.add (h₂.space_polyBounded.comp hlen)) fun a => ?_
  rw [comp_time]; have := ht₁ a; have := ht₂ (f a); nlinarith

/-- **Polynomial-time postprocessing** preserves the factor when `1 ≤ K a`. -/
theorem comp_ofPolyTime (h : c.FactorTimePolySpace K) (hK : ∀ a, 1 ≤ K a) {r : β → γ}
    (hr : ComputableInPolyTime r eβ eγ) :
    ((NativeCertificate.ofPolyTime hr).comp c).FactorTimePolySpace K :=
  (h.comp (ofPolyTime hr)).mono_const 2 fun a => by have := hK a; omega

/-- **Polynomial-time preprocessing** pulls back the factor when `1 ≤ K₂ (f a)`. -/
theorem comp_polyPre {r : β → γ} {c₂ : NativeCertificate r eβ eγ} {K₂ : β → ℕ}
    (h : c₂.FactorTimePolySpace K₂) (hf : ComputableInPolyTime f enc eβ)
    (hK : ∀ a, 1 ≤ K₂ (f a)) :
    (c₂.comp (NativeCertificate.ofPolyTime hf)).FactorTimePolySpace (fun a => K₂ (f a)) :=
  ((ofPolyTime hf).comp h).mono_const 2 fun a => by have := hK a; omega

/-- **Selected-branch conditional**: the `yes` factor need only be bounded by `K` where `condition`
holds. -/
theorem branch {condition : α → Bool} {f₁ f₂ : α → β}
    {test : NativeCertificate condition enc encBool}
    {yes : NativeCertificate f₁ enc eβ} {no : NativeCertificate f₂ enc eβ} {Ky : α → ℕ}
    (ht : test.FactorTimePolySpace K) (hy : yes.FactorTimePolySpace Ky)
    (hcond : ∀ a, condition a = true → Ky a ≤ K a) (hn : no.FactorTimePolySpace K) :
    (NativeCertificate.branch test yes no).FactorTimePolySpace K := by
  obtain ⟨Tt, hTt, htt⟩ := ht.exists_time_polyBounded
  obtain ⟨Ty, hTy, hyt⟩ := hy.exists_time_polyBounded
  obtain ⟨Tn, hTn, hnt⟩ := hn.exists_time_polyBounded
  refine of_polyBounded (hTt.add (hTy.add hTn))
    ((ht.space_polyBounded.add (hy.space_polyBounded.add hn.space_polyBounded)).mono
      fun a => by rw [branch_space]; split <;> omega) fun a => ?_
  rw [branch_time]; split
  · have := htt a; have := (hyt a).trans (Nat.mul_le_mul_right _ (hcond a ‹_›)); nlinarith
  · have := htt a; have := hnt a; nlinarith

/-- **Retained-input option elimination**: the `some` factor need only be bounded by `K a` on pairs
`(a, b)` with `value a = Option.some b`, whose encoded length is polynomially bounded by `cVal`'s
workspace. -/
theorem option {value : α → Option β} {fallback : α → γ} {body : α × β → γ}
    {cVal : NativeCertificate value enc (encOption eβ)}
    {cNone : NativeCertificate fallback enc eγ}
    {cSome : NativeCertificate body (encPair enc eβ) eγ} {Ksome : α × β → ℕ}
    (hK : ∀ a, 1 ≤ K a) (hval : cVal.FactorTimePolySpace K)
    (hnone : cNone.FactorTimePolySpace K) (hsome : cSome.FactorTimePolySpace Ksome)
    (hcond : ∀ a b, value a = Option.some b → Ksome (a, b) ≤ K a) :
    (NativeCertificate.option cVal cNone cSome).FactorTimePolySpace K := by
  have hvs := hval.space_polyBounded; have hlen := polyBounded_length_of_space hvs
  obtain ⟨Tv, hTv, hvt⟩ := hval.exists_time_polyBounded
  obtain ⟨Tn, hTn, hnt⟩ := hnone.exists_time_polyBounded
  obtain ⟨Ts, hTs, hst⟩ := hsome.exists_time_polyBounded
  refine of_polyBounded
    ((((PolyBounded.const 2).mul hTv).add .self).add (polyBounded_optionElim hlen hTn hTs))
    ((((PolyBounded.const 2).mul hvs).add .self).add
      (polyBounded_optionElim hlen hnone.space_polyBounded hsome.space_polyBounded)) fun a => ?_
  rw [option_time]; have := hK a; have := hvt a
  cases hva : value a with
  | none => simp only [Option.elim_none]; have := hnt a; nlinarith
  | some b =>
    simp only [Option.elim_some]
    have := (hst (a, b)).trans (Nat.mul_le_mul_right _ (hcond a b hva)); nlinarith

theorem computableInPolySpace (h : c.FactorTimePolySpace K) :
    ComputableInPolySpace f enc eβ :=
  c.computableInPolySpace h.space_polyBounded

/-- When the factor `K` is itself polynomially bounded, the certificate computes `f` in polynomial
time. -/
theorem polyTime (h : c.FactorTimePolySpace K) (hK : PolyBounded (fun a => (enc a).length) K) :
    ComputableInPolyTime f enc eβ := by
  obtain ⟨T, hT, ht⟩ := h.exists_time_polyBounded
  exact c.polyTime ⟨(hK.mul hT).mono ht, h.space_polyBounded⟩

/-- Extract a single monotone polynomial `poly` bounding `c.time a ≤ K a * poly n` and
`c.space a ≤ poly n`. -/
theorem exists_mono_poly (h : c.FactorTimePolySpace K) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧ Monotone poly ∧
      ∀ a, c.time a ≤ K a * poly (enc a).length ∧ c.space a ≤ poly (enc a).length := by
  obtain ⟨C, d, h⟩ := h
  refine ⟨fun n => C * (n + 1) ^ d,
    (Cslib.PolynomiallyBounded.const C).mul ((Cslib.PolynomiallyBounded.id.add (.const 1)).pow d),
    fun _ _ hxy => Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right hxy 1) d),
    fun a => ⟨(h a).1.trans_eq (by ring), (h a).2⟩⟩

/-- **The machine bounds** of a certificate in time `K` times a polynomial and polynomial space. -/
theorem computableInO (h : c.FactorTimePolySpace K) : ∃ e : ℕ,
    ComputableInO f enc eβ (fun a => K a * ((enc a).length + 1) ^ e)
      (fun a => ((enc a).length + 1) ^ e) := by
  obtain ⟨C, d, h⟩ := h
  refine ⟨d, c.computes.mono C (fun a => (h a).1.trans ?_) (fun a => (h a).2.trans ?_)⟩
  · rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
  · exact Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- Existential polynomial form of `computableInO`. -/
theorem exists_poly_computableInO (h : c.FactorTimePolySpace K) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO f enc eβ (fun a => K a * poly (enc a).length)
        (fun a => poly (enc a).length) :=
  let ⟨e, hc⟩ := h.computableInO
  ⟨fun n => (n + 1) ^ e, (Cslib.PolynomiallyBounded.id.add (.const 1)).pow e, hc⟩

end FactorTimePolySpace

/-- A certificate **runs in time `2 ^ E` times a polynomial and in polynomial space**: for constants
`C` and `d`, its time is at most `C 2 ^ E a (n + 1) ^ d` and its space at most `C (n + 1) ^ d` on
inputs `a` of encoded length `n`. -/
@[expose] def ExpTimePolySpace (c : NativeCertificate f enc eβ) (E : α → ℕ) : Prop :=
  c.FactorTimePolySpace (fun a => 2 ^ E a)

namespace ExpTimePolySpace

variable {c : NativeCertificate f enc eβ} {E E' : α → ℕ}

theorem mono (h : c.ExpTimePolySpace E) (hE : ∀ a, E a ≤ E' a) : c.ExpTimePolySpace E' :=
  FactorTimePolySpace.mono h fun a => Nat.pow_le_pow_right (by norm_num) (hE a)

/-- **Pairs add the exponents.** -/
theorem prod {c' : NativeCertificate g enc eγ} (h : c.ExpTimePolySpace E)
    (h' : c'.ExpTimePolySpace E') : (c.prod c').ExpTimePolySpace fun a => E a + E' a :=
  (FactorTimePolySpace.prod h h').mono_const 2 fun a => by
    rw [pow_add]
    have := Nat.le_mul_of_pos_right (2 ^ E a) (Nat.two_pow_pos (E' a))
    have := Nat.le_mul_of_pos_left (2 ^ E' a) (Nat.two_pow_pos (E a)); omega

/-- **Polynomial-time postprocessing keeps the shape**: the polynomial space bound also bounds the
encoded intermediate value, on which the postprocessing runs. -/
theorem comp_ofPolyTime (h : c.ExpTimePolySpace E) {r : β → γ}
    (hr : ComputableInPolyTime r eβ eγ) : ((ofPolyTime hr).comp c).ExpTimePolySpace E :=
  FactorTimePolySpace.comp_ofPolyTime h (fun _ => Nat.two_pow_pos _) hr

/-- **The machine bounds** of a certificate in time `2 ^ E` times a polynomial and polynomial
space. -/
theorem computableInO (h : c.ExpTimePolySpace E) : ∃ e : ℕ,
    ComputableInO f enc eβ (fun a => 2 ^ E a * ((enc a).length + 1) ^ e)
      (fun a => ((enc a).length + 1) ^ e) :=
  FactorTimePolySpace.computableInO h

end ExpTimePolySpace

/-- **Polynomial-time certificates** run in time `2 ^ E` times a polynomial for every `E`. -/
theorem expTimePolySpace_ofPolyTime (hf : ComputableInPolyTime f enc eβ) (E : α → ℕ) :
    (ofPolyTime hf).ExpTimePolySpace E :=
  (FactorTimePolySpace.ofPolyTime hf).mono fun _ => Nat.two_pow_pos _

/-- **A branch whose `yes` side runs in time `2 ^ N` times a polynomial** runs in polynomial space
and in time `2 ^ N` times a polynomial, when the test and the `no` side are polynomial and the
`yes` side has polynomial space. The `yes` time bound is needed only where `condition` holds. The
polynomial factor `T` is left implicit, unlike the explicit constants of `ExpTimePolySpace`. -/
theorem branch_bounds_of_two_pow {condition : α → Bool} {f₁ f₂ : α → β}
    {test : NativeCertificate condition enc encBool}
    {yes : NativeCertificate f₁ enc eβ} {no : NativeCertificate f₂ enc eβ}
    (ht : test.IsPolynomial) (hn : no.IsPolynomial)
    (hys : PolyBounded (fun a => (enc a).length) yes.space)
    {N Ty : α → ℕ} (hTy : PolyBounded (fun a => (enc a).length) Ty)
    (hyt : ∀ a, condition a = true → yes.time a ≤ 2 ^ N a * Ty a) :
    PolyBounded (fun a => (enc a).length) (branch test yes no).space ∧
      ∃ T : α → ℕ, PolyBounded (fun a => (enc a).length) T ∧
        ∀ a, (branch test yes no).time a ≤ 2 ^ N a * T a := by
  refine ⟨(ht.2.add (hys.add hn.2)).mono fun a => by simp only [branch_space]; split <;> omega,
    fun a => test.time a + no.time a + Ty a, (ht.1.add hn.1).add hTy, fun a => ?_⟩
  have h1 : 1 ≤ 2 ^ N a := Nat.one_le_two_pow
  simp only [branch_time]; split
  · have := hyt a ‹_›; nlinarith
  · nlinarith

end Cslib.GenericRAM.NativeCertificate
