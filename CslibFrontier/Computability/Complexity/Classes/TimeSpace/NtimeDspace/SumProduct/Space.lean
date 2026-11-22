/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.Machine
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.NatList

/-!
# The evaluator's states are small

Every state the evaluator reaches satisfies `Inv`: each frame on the stack
belongs to a valid node of the recursion and holds numbers bounded by that
node's precision and index length (`FrameOK`). The encoded length of such a stack
is at most `17` times the cost of the recursion (`stackLen_le`), which is the
space bound of Proposition 3.2.

The time bound needs no step counting. A deterministic process on numbers below
`2^X` that reaches a fixed point does so within `2^X` steps
(`iterate_eq_of_fixed`).

## Main results

* `inv_step`: the invariant is preserved by a step.
* `code_lt`: the code of a state satisfying the invariant is below `2^X` with
  `X = 34·cost + 2·size V + 12`.
* `iterate_eq_of_fixed`: the pigeonhole bound on the halting time.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open SPTree NatList

/-- The fields of a frame, as a list. -/
def Frame.toList (f : Frame) : List ℕ := [f.k, f.j, f.l, f.c]

/-- The frames, flattened top first. -/
def flatFrames (fr : List Frame) : List ℕ := fr.flatMap Frame.toList

/-- The code of a state. -/
def State.code (st : State) : ℕ :=
  enc [st.call.toNat, st.v, enc (flatFrames st.frames), enc st.path]

/-- The numbers a frame holds are bounded by its node. -/
def FrameOK : SPTree → ℕ → Frame → Prop
  | leaf _ _, _, _ => False
  | sum P w _, i, f => f.k < P ∧ f.j ≤ f.k ∧ i < 2 ^ w ∧ f.l = 0 ∧ f.c ≤ 2 ^ w + i
  | prod P _ _, i, f => f.k < P ∧ f.j ≤ f.k ∧ i < 2 ∧ f.l ≤ f.j ∧ f.c ≤ f.k + 1 + f.l
  | shift P _ _, i, f => f.k < P ∧ i = 0 ∧ f.j = 0 ∧ f.l = 0 ∧ f.c = 0

theorem FrameOK.validChild {u : SPTree} {i : ℕ} {f : Frame} (h : FrameOK u i f) :
    u.ValidChild i := by
  cases u with
  | leaf => exact h.elim
  | sum => exact h.2.2.1
  | prod => exact h.2.2.1
  | shift => exact h.2.1

/-- Every frame belongs to the node below its symbol. -/
def StackOK (t : SPTree) : List Frame → List ℕ → Prop
  | [], [] => True
  | f :: fr, i :: π => StackOK t fr π ∧ FrameOK (node t π) i f
  | _, _ => False

theorem StackOK.valid {t : SPTree} : ∀ {fr : List Frame} {π : List ℕ}, StackOK t fr π → Valid t π
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hf⟩ => ⟨h.valid, hf.validChild⟩

/-- The invariant of the evaluator. -/
def Inv (t : SPTree) (V : ℕ) (st : State) : Prop :=
  StackOK t st.frames st.path ∧ (st.call = true → st.v ≤ V) ∧ (st.call = false → st.v ≤ 1)

section Preservation

variable {q : List ℕ → Info} {lb : List ℕ → ℕ → Bool} {t : SPTree} {V : ℕ}

theorem advanceProd_inv {P : ℕ} {a b : SPTree} {ρ : List ℕ} {fr : List Frame}
    (hnode : node t ρ = prod P a b) (hfr : StackOK t fr ρ) (hPV : P ≤ V)
    {k j l c : ℕ} (hk : k < P) (hj : j ≤ k) (hl : l ≤ j) (hc : c ≤ k + 1 + l + 1) :
    Inv t V (advanceProd k j l c fr ρ) := by
  unfold advanceProd
  split_ifs with h1 h2
  · refine ⟨⟨hfr, ?_⟩, fun _ => by simp; omega, fun h => absurd h (by simp)⟩
    rw [hnode]; exact ⟨hk, hj, by omega, by simp; omega, by simp; omega⟩
  · refine ⟨⟨hfr, ?_⟩, fun _ => by simp, fun h => absurd h (by simp)⟩
    rw [hnode]; exact ⟨hk, by simp; omega, by omega, by simp, by simp; omega⟩
  · exact ⟨hfr, fun h => absurd h (by simp), fun _ => by simp; omega⟩

/-- **The invariant is preserved.** -/
theorem inv_step (hq : ∀ π, Valid t π → q π = (node t π).info)
    (hV : ∀ π, Valid t π → (node t π).prec + (node t π).param ≤ V)
    {st : State} (h : Inv t V st) : Inv t V (step q lb st) := by
  obtain ⟨call, v, fr, π⟩ := st
  obtain ⟨hs, hcall, hret⟩ := h
  cases call with
  | true =>
    have hπ := hs.valid
    have hvV : v ≤ V := hcall rfl
    have hqπ := hq π hπ
    have hVπ := hV π hπ
    simp only [step, hqπ, SPTree.info]
    generalize hu : node t π = u at hqπ hVπ ⊢
    split_ifs with h1 h2 h3 h4
    · exact ⟨hs, fun h => absurd h (by simp), fun _ => by simp⟩
    · exact ⟨hs, fun h => absurd h (by simp), fun _ => Bool.toNat_le _⟩
    · refine ⟨⟨hs, ?_⟩, fun _ => by simp, fun h => absurd h (by simp)⟩
      rw [hu]
      cases u with
      | leaf => simp [SPTree.tag] at h2
      | sum P w f =>
        simp only [SPTree.prec] at h1
        exact ⟨by dsimp only; omega, by simp, Nat.one_le_two_pow, rfl, by simp⟩
      | prod P a b =>
        simp only [SPTree.prec] at h1
        exact ⟨by dsimp only; omega, by simp, by omega, by simp, by simp⟩
      | shift => simp [SPTree.tag] at h3
    · refine ⟨⟨hs, ?_⟩, fun _ => ?_, fun h => absurd h (by simp)⟩
      · rw [hu]
        cases u with
        | shift P σ a =>
          simp only [SPTree.prec] at h1
          exact ⟨by dsimp only; omega, rfl, rfl, rfl, rfl⟩
        | _ => simp [SPTree.tag] at h4
      · simp only [SPTree.prec, SPTree.param] at hVπ h1 ⊢
        cases u with
        | shift P σ a => simp only [SPTree.prec, SPTree.param] at hVπ h1 ⊢; omega
        | _ => simp [SPTree.tag] at h4
    · exact ⟨hs, fun h => absurd h (by simp), fun _ => by simp⟩
  | false =>
    have hb : v ≤ 1 := hret rfl
    cases fr with
    | nil => exact ⟨hs, hcall, hret⟩
    | cons f fr =>
      cases π with
      | nil => exact hs.elim
      | cons i ρ =>
        obtain ⟨hfr, hf⟩ := hs
        have hρ := hfr.valid
        have hqρ := hq ρ hρ
        have hVρ := hV ρ hρ
        obtain ⟨k, j, l, c⟩ := f
        simp only [step, List.tail_cons, List.headD_cons, hqρ, SPTree.info]
        generalize hu : node t ρ = u at hqρ hVρ hf ⊢
        cases u with
        | leaf => exact hf.elim
        | sum P w g =>
          obtain ⟨hk, hj, hi, hl, hc⟩ := hf
          dsimp only at hk hj hl hc
          simp only [SPTree.tag, SPTree.param, SPTree.prec, ite_true] at hVρ ⊢
          by_cases h1 : i + 1 < 2 ^ w
          · simp only [h1, ↓reduceIte]
            refine ⟨⟨hfr, ?_⟩, fun _ => by dsimp only; omega, fun h => absurd h (by simp)⟩
            rw [hu]; exact ⟨hk, hj, h1, hl, by dsimp only; omega⟩
          · simp only [h1, ↓reduceIte]
            by_cases h2 : j < k
            · simp only [h2, ↓reduceIte]
              refine ⟨⟨hfr, ?_⟩, fun _ => by dsimp only; omega, fun h => absurd h (by simp)⟩
              rw [hu]
              refine ⟨hk, by dsimp only; omega, Nat.one_le_two_pow, hl, ?_⟩
              dsimp only
              have : i + 1 = 2 ^ w := by omega
              omega
            · simp only [h2, ↓reduceIte]
              exact ⟨hfr, fun h => absurd h (by simp), fun _ => by dsimp only; omega⟩
        | prod P a b =>
          obtain ⟨hk, hj, hi, hl, hc⟩ := hf
          dsimp only at hk hj hl hc
          simp only [SPTree.tag, SPTree.prec, OfNat.ofNat_ne_one, ite_false, ite_true] at hVρ ⊢
          by_cases h1 : i = 0
          · simp only [h1, ↓reduceIte]
            by_cases h2 : v = 0
            · simp only [h2, ↓reduceIte]
              exact advanceProd_inv hu hfr (by omega) hk hj hl (by omega)
            · simp only [h2, ↓reduceIte]
              refine ⟨⟨hfr, ?_⟩, fun _ => by dsimp only; omega, fun h => absurd h (by simp)⟩
              rw [hu]; exact ⟨hk, hj, by omega, hl, hc⟩
          · simp only [h1, ↓reduceIte]
            exact advanceProd_inv hu hfr (by omega) hk hj hl (by omega)
        | shift P σ a =>
          simp only [SPTree.tag, OfNat.ofNat_ne_one, ite_false]
          exact ⟨hfr, fun h => absurd h (by simp), fun _ => hb⟩

theorem inv_iterate (hq : ∀ π, Valid t π → q π = (node t π).info)
    (hV : ∀ π, Valid t π → (node t π).prec + (node t π).param ≤ V) {st : State}
    (h : Inv t V st) (n : ℕ) : Inv t V ((step q lb)^[n] st) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [Function.iterate_succ_apply']; exact inv_step hq hV ih

end Preservation

/-! ### The size of a state -/

/-- The encoded length of one entry. -/
def entryLen (x : ℕ) : ℕ := 2 * x.size + 1

/-- The encoded length of a frame together with its symbol. -/
def frameLen (f : Frame) (i : ℕ) : ℕ :=
  entryLen f.k + entryLen f.j + entryLen f.l + entryLen f.c + entryLen i

/-- The encoded length of a stack. -/
def stackLen : List Frame → List ℕ → ℕ
  | f :: fr, i :: π => frameLen f i + stackLen fr π
  | _, _ => 0

theorem size_le_of_lt {x m : ℕ} (h : x < 2 ^ m) : x.size ≤ m := Nat.size_le.mpr h

theorem size_le_of_le_pow {x m : ℕ} (h : x ≤ 2 ^ m - 1) : x.size ≤ m :=
  size_le_of_lt (by have := Nat.one_le_two_pow (n := m); omega)

theorem frameLen_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {u : SPTree} (hP : u.prec ≤ 2 ^ ℓ) {i : ℕ} {f : Frame}
    (h : FrameOK u i f) : frameLen f i ≤ 17 * u.nodeCost ℓ := by
  obtain ⟨k, j, l, c⟩ := f
  unfold frameLen entryLen
  cases u with
  | leaf => exact h.elim
  | sum P w g =>
    obtain ⟨hk, hj, hi, hl, hc⟩ := h
    simp only [SPTree.prec, SPTree.nodeCost] at hP hk hj hl hc ⊢
    subst hl
    have h1 := size_le_of_lt (show k < 2 ^ ℓ by omega)
    have h2 := size_le_of_lt (show j < 2 ^ ℓ by omega)
    have h3 := size_le_of_lt (show c < 2 ^ (w + 1) by rw [pow_succ]; omega)
    have h4 := size_le_of_lt hi
    simp only [Nat.size_zero]
    omega
  | prod P a b =>
    obtain ⟨hk, hj, hi, hl, hc⟩ := h
    simp only [SPTree.prec, SPTree.nodeCost] at hP hk hj hl hc ⊢
    have h1 := size_le_of_lt (show k < 2 ^ ℓ by omega)
    have h2 := size_le_of_lt (show j < 2 ^ ℓ by omega)
    have h3 := size_le_of_lt (show l < 2 ^ ℓ by omega)
    have h4 := size_le_of_lt (show c < 2 ^ (ℓ + 1) by rw [pow_succ]; omega)
    have h5 := size_le_of_lt (show i < 2 ^ 1 by omega)
    omega
  | shift P σ a =>
    obtain ⟨hk, hi, hj, hl, hc⟩ := h
    simp only [SPTree.prec, SPTree.nodeCost] at hP hk hj hl hc hi ⊢
    subst hi hj hl hc
    have h1 := size_le_of_lt (show k < 2 ^ ℓ by omega)
    simp only [Nat.size_zero]
    omega

/-- **The stack is paid for by the cost.** -/
theorem stackLen_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {t : SPTree} (hP : t.PrecLe (2 ^ ℓ)) :
    ∀ {fr : List Frame} {π : List ℕ}, StackOK t fr π →
      stackLen fr π + 17 * (node t π).cost ℓ ≤ 17 * t.cost ℓ
  | [], [], _ => by simp [stackLen]
  | f :: fr, i :: π, ⟨hs, hf⟩ => by
    have ih := stackLen_le hℓ hP hs
    have hc := cost_child ℓ hf.validChild
    have hfl := frameLen_le hℓ (hP.node hs.valid).prec hf
    simp only [stackLen, node_cons]
    omega

theorem elen_flat_add (t : SPTree) : ∀ {fr : List Frame} {π : List ℕ}, StackOK t fr π →
    elen (flatFrames fr) + elen π = 2 + stackLen fr π
  | [], [], _ => rfl
  | f :: fr, i :: π, ⟨hs, _⟩ => by
    have ih := elen_flat_add t hs
    simp only [stackLen, frameLen, entryLen, flatFrames, List.flatMap_cons, Frame.toList,
      List.cons_append, List.nil_append, elen_cons]
    simp only [flatFrames] at ih
    omega

/-- **The code of a reachable state is small.** -/
theorem code_lt {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {t : SPTree} (hP : t.PrecLe (2 ^ ℓ)) {V : ℕ}
    {st : State} (h : Inv t V st) :
    st.code < 2 ^ (34 * t.cost ℓ + 2 * V.size + 16) := by
  obtain ⟨hs, hcall, hret⟩ := h
  have hlen := elen_flat_add t hs
  have hstack := stackLen_le hℓ hP hs
  have hv : st.v.size ≤ V.size + 1 := by
    cases hc : st.call
    · have := hret hc
      exact (size_le_of_lt (show st.v < 2 ^ 1 by omega)).trans (by omega)
    · exact (Nat.size_le_size (hcall hc)).trans (by omega)
  have hb : st.call.toNat.size ≤ 1 := size_le_of_lt (by cases st.call <;> simp)
  have hA := size_enc_le (flatFrames st.frames)
  have hB := size_enc_le st.path
  refine (enc_lt _).trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
  simp only [elen_cons, elen_nil]
  omega

/-! ### Halting within `2^X` steps -/

/-- **Pigeonhole.** If every iterate of `x` is below `N` and some iterate is a
fixed point `y`, then the `N`th iterate is `y`. -/
theorem iterate_eq_of_fixed (g : ℕ → ℕ) (x y N : ℕ) (hb : ∀ n, g^[n] x < N)
    (hy : g y = y) (hreach : ∃ n, g^[n] x = y) : g^[N] x = y := by
  classical
  have hfix : ∀ m n, g^[n] x = y → g^[n + m] x = y := by
    intro m n hn
    induction m with
    | zero => exact hn
    | succ m ih => rw [← Nat.add_assoc, Function.iterate_succ_apply', ih, hy]
  let n0 := Nat.find hreach
  have hn0 : g^[n0] x = y := Nat.find_spec hreach
  by_cases hle : n0 ≤ N
  · have := hfix (N - n0) n0 hn0
    rwa [Nat.add_sub_cancel' hle] at this
  · exfalso
    -- Two of the first `N + 1` iterates agree.
    obtain ⟨a, ha, b, hb', hne, hab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (N + 1)) (t := Finset.range N) (f := fun n => g^[n] x)
      (by simp) (fun n _ => by simpa using hb n)
    simp only [Finset.mem_range] at ha hb'
    wlog hlt : a < b generalizing a b
    · exact this b a (Ne.symm hne) hab.symm hb' ha (by omega)
    -- The orbit is periodic with period `b - a` from `a` on.
    have hper : ∀ n, a ≤ n → g^[n + (b - a)] x = g^[n] x := by
      intro n hn
      have e1 : n + (b - a) = (n - a) + b := by omega
      have e2 : n = (n - a) + a := by omega
      rw [e1, Function.iterate_add_apply, ← hab, ← Function.iterate_add_apply, ← e2]
    have hlt0 : n0 - (b - a) < n0 := by omega
    have : g^[n0 - (b - a)] x = y := by
      rw [← hn0, ← hper (n0 - (b - a)) (by omega), Nat.sub_add_cancel (by omega)]
    exact Nat.find_min hreach hlt0 this

end Cslib.Complexity.NtimeDspace.SumProduct
