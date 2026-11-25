/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation.SavitchEndpoints
public import CslibFrontier.Computability.Complexity.Classes.Constructible
import CslibFrontier.Computability.Complexity.Classes.Constructible.UnaryClock
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.CodeEdge
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.WordTransducers
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Nondeterministic space in alternating time for time-constructible bounds

A play of Savitch's midpoint game on the views of a nondeterministic machine `ntm` ends with the
edge test of two endpoints, each the midpoint of the last level with a given half or, if there is
none, the code of the initial view or the accepting code
(`Cslib.Reachability.midpointGame_eq_reach_lastMidpoint`). This file names that last test,
`Turing.MultiTapeNTM.midpointLeaf`, on the width, the input and the two endpoints as options, and
assembles a verifier of the midpoint game within time `O((n + s n) ^ 2)` from the edge test of
codes, `Turing.MultiTapeNTM.codeEdge`: the width and the number of moves in unary
(`Cslib.Complexity.TimeConstructible.computableInO_unary_of_polyTime`), both endpoints
(`Cslib.Reachability.computableInO_lastMidpoint`), the code of the initial view and the accepting
code within linear time, and the comparison of the endpoints within quadratic time
(`Turing.MultiTapeNTM.computableInO_midpointLeaf`).

The result, `Cslib.Complexity.NSPACE_subset_ATIME_sq_of_timeConstructible`, proves
`NSPACE s ⊆ ATIME ((n + s n) ^ 2)` for a time-constructible `s`: a step toward [Chandra, Kozen and
Stockmeyer, Theorem 3.1][ChandraKozenStockmeyer1981] (`NSPACE(S) ⊆ ⋃_{c > 0} ATIME(c * S ^ 2)` for
`S(n) ≥ n` without a constructibility hypothesis on `S`, tracked in #4086). The edge test decodes
two views, and compares the second with the results of the finitely many actions the machine
permits on the first, within quadratic time (`Turing.MultiTapeNTM.computableInO_codeEdge`).

The views record the input, so the codes have width linear in `n + s n`, and the bound is
`O((n + s n) ^ 2)` (Sipser's form) for every `s`; under the hypothesis `s n ≥ n` of Theorem 3.1 it
is `O(s n ^ 2)`. Unlike Theorem 3.1, `s` is assumed time-constructible here to write the number of
moves in unary (#4086).

## Main definitions

* `Turing.MultiTapeNTM.midpointLeaf`: the leaf test of the midpoint game on the views of a machine.

## Main results

* `Turing.MultiTapeNTM.computableInO_midpointLeaf`: the leaf test runs within quadratic time.
* `Cslib.Complexity.NSPACE_subset_ATIME_sq_of_timeConstructible`: `NSPACE s ⊆ ATIME ((n + s n) ^ 2)`
  for a time-constructible `s` (time-constructible step toward CKS Theorem 3.1; #4086).

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State]

/-- **The leaf test of Savitch's midpoint game** on the views of `ntm`, at width `w` on `input`,
given the final endpoints `u` and `v` of a play as options: the edge test
`Cslib.Reachability.reach ntm.codeEdge (2 * w + 2) 0` of the left endpoint, by default the code of
the initial view on `input`, and of the right endpoint, by default the accepting code. -/
noncomputable def midpointLeaf (ntm : MultiTapeNTM k Bool State) (w : ℕ) (input : List Bool)
    (u v : Option (List Bool)) : Bool :=
  Cslib.Reachability.reach ntm.codeEdge (2 * w + 2) 0 (u.getD (viewCode w (ntm.initView input)))
    (v.getD (acceptCode w))

/-- The encoding of an initial view is the framed input, then a word fixed by the initial state. -/
private theorem encFiniteCfg_init (q : State) (input : List Bool) :
    encFiniteCfg (FiniteCfg.init (k := k) q input) =
      frame input ++ encPair (encFinite (Option State))
        (encPair encUnary (encPair (encPi (encBiTape encBool)) encBits))
        (some q, 1, fun _ : Fin k => Cslib.Turing.BiTape.nil, []) := by
  simp only [encFiniteCfg_apply, FiniteCfg.init, Fin.val_one, encPair_apply, encBits_apply]

/-- The padding of a code: twice `w - m` zeros, from two copies of `w` ones with `m` dropped. -/
private theorem map_drop_append_drop (w m : ℕ) :
    List.map (fun _ => false) ((List.replicate w true).drop m ++ (List.replicate w true).drop m) =
      List.replicate (2 * (w - m)) false := by
  simp only [List.drop_replicate, List.map_replicate, ← List.replicate_add, two_mul]

/-- Replacing every bit by `false` within linear time and space. -/
private theorem computableInO_map_false :
    ComputableInO (List.map fun _ => false) encBits encBits (fun l => (encBits l).length)
      fun l => (encBits l).length :=
  .of_bounds (ComputableInTimeAndSpace.map_bits _) 12 (fun l => by simp only [encBits_apply]; omega)
    (fun _ => Nat.zero_le _) fun l => by simp only [encBits_apply, List.length_map]; omega

/-- **The leaf test of the midpoint game runs within quadratic time** in the length of its encoded
input: the edge test of codes is quadratic (`Turing.MultiTapeNTM.computableInO_codeEdge`), the code
of the initial view and the accepting code are written within linear time, and the two endpoints
are compared within quadratic time (`Turing.MultiTapeTM.ComputableInO.eq'`). -/
theorem computableInO_midpointLeaf (ntm : MultiTapeNTM k Bool State) :
    ComputableInO
      (fun ((w, input, u, v) : ℕ × List Bool × Option (List Bool) × Option (List Bool)) =>
        ntm.midpointLeaf w input u v)
      (encPair encUnary (encPair encBits (encPair (encOption encBits) (encOption encBits))))
      encBool
      (fun p => (encPair encUnary (encPair encBits (encPair (encOption encBits)
        (encOption encBits))) p).length ^ 2)
      fun p => (encPair encUnary (encPair encBits (encPair (encOption encBits)
        (encOption encBits))) p).length ^ 2 := by
  have hedge := ntm.computableInO_codeEdge
  let P := ℕ × List Bool × Option (List Bool) × Option (List Bool)
  set E := encPair encUnary (encPair encBits (encPair (encOption encBits) (encOption encBits)))
    with hE
  set N := fun p : P => (E p).length with hN
  -- the components of the input
  have h₂ : ComputableInO Prod.snd E
      (encPair encBits (encPair (encOption encBits) (encOption encBits))) N N :=
    ComputableInO.snd _ _
  have hinput := ComputableInO.fst' h₂
  have hu := ComputableInO.fst' (ComputableInO.snd' h₂)
  have hv := ComputableInO.snd' (ComputableInO.snd' h₂)
  have hones : ComputableInO (fun p : P => List.replicate p.1 true) E encBits N N :=
    (ComputableInO.fst encUnary _).of_enc_eq fun _ => rfl
  -- the encoding of the initial view, and the code of the initial view
  have hview := (hinput.frame'.bitsAppend' (ComputableInO.const (encIn := E) (encMid := encBits)
    (encPair (encFinite (Option State))
      (encPair encUnary (encPair (encPi (encBiTape encBool)) encBits))
      (some ntm.q₀, 1, fun _ : Fin k => Cslib.Turing.BiTape.nil, [])))).of_enc_eq (encC := encBits)
    (g := fun p : P => encFiniteCfg (ntm.initView (k := k) p.2.1))
    fun p => encFiniteCfg_init ntm.q₀ p.2.1
  have hdrop := (ComputableInDegree.bitsDrop.inO_one).comp_linear
    (hones.prod hview.bitsLengthUnary')
  have hzeros := (computableInO_map_false.comp_linear (hdrop.bitsAppend' hdrop)).of_enc_eq
    (encC := encBits)
    (g := fun p : P =>
      List.replicate (2 * (p.1 - (encFiniteCfg (ntm.initView (k := k) p.2.1)).length)) false)
    fun p => (map_drop_append_drop _ _).symm
  have hcode := (((ComputableInO.const (encIn := E) (encMid := encBits) [false]).bitsAppend'
    (hview.frame'.bitsAppend' hzeros)).of_enc_eq (encC := encBits)
    (g := fun p : P => viewCode p.1 (ntm.initView p.2.1))
    fun _ => rfl).mono (T' := N) (S' := N) 12
    (fun p => by simp only [hN]; omega) fun p => by simp only [hN]; omega
  have haccept := (((hones.bitsAppend' hones).bitsAppend'
    (ComputableInO.const (encIn := E) (encMid := encBits) [true, true])).of_enc_eq (encC := encBits)
    (g := fun p : P => acceptCode p.1) fun p => by
      simp only [acceptCode, encBits_apply, two_mul, List.replicate_add]; rfl).mono
    (T' := N) (S' := N) 4
    (fun p => by simp only [hN]; omega)
    fun p => by simp only [hN]; omega
  -- the endpoints, each a given word or its default
  have hbound (p : P) (o : Option (List Bool)) (ho : (encOption encBits o).length ≤ N p) :
      N p + N p + ((encPair E (encOption encBits) (p, o)).length +
        o.elim (N p) fun x => (encPair E encBits (p, x)).length) ≤ 8 * (N p + 1) := by
    rcases o with _ | x <;>
      simp only [length_encPair, Option.elim, encBits_apply, encOption_some, List.length_cons, hN]
        at ho ⊢ <;> omega
  have hlenu (p : P) : (encOption encBits p.2.2.1).length ≤ N p := by
    obtain ⟨_, _, _, _⟩ := p
    simp only [hN, hE, length_encPair]; omega
  have hlenv (p : P) : (encOption encBits p.2.2.2).length ≤ N p := by
    obtain ⟨_, _, _, _⟩ := p
    simp only [hN, hE, length_encPair]; omega
  have ha := (((ComputableInO.optionElimSnd hcode (ComputableInO.snd E encBits)).comp
    ((ComputableInO.id' (encMid := E)).prod hu)).of_enc_eq (encC := encBits)
    (g := fun p : P => p.2.2.1.getD (viewCode p.1 (ntm.initView p.2.1)))
    fun p => by obtain ⟨_, _, _ | _, _⟩ := p <;> rfl).mono (T' := N) (S' := N) 8
    (fun p => hbound p _ (hlenu p)) fun p => hbound p _ (hlenu p)
  have hb := (((ComputableInO.optionElimSnd haccept (ComputableInO.snd E encBits)).comp
    ((ComputableInO.id' (encMid := E)).prod hv)).of_enc_eq (encC := encBits)
    (g := fun p : P => p.2.2.2.getD (acceptCode p.1))
    fun p => by obtain ⟨_, _, _, _ | _⟩ := p <;> rfl).mono (T' := N) (S' := N) 8
    (fun p => hbound p _ (hlenv p)) fun p => hbound p _ (hlenv p)
  -- the edge test of the endpoints
  obtain ⟨ca, hca⟩ := ha.length_le
  obtain ⟨cb, hcb⟩ := hb.length_le
  have hbd (A B M : ℕ) (hA : A ≤ ca * (M + 1)) (hB : B ≤ cb * (M + 1)) :
      M + M + (A + 1) * (A + B + 1) + (M + M + (2 * A + 1 + B) ^ 2) ≤
        96 * (ca + cb + 1) ^ 2 * (M ^ 2 + 1) := by
    set c := ca + cb + 1
    have hAc : A ≤ c * (M + 1) := hA.trans (Nat.mul_le_mul_right _ (by omega))
    have hBc : B ≤ c * (M + 1) := hB.trans (Nat.mul_le_mul_right _ (by omega))
    have hc : M + 1 ≤ c * (M + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have h4c : 4 * c * (M + 1) = 4 * (c * (M + 1)) := by ring
    have h12 : (A + 1) * (A + B + 1) ≤ (4 * c * (M + 1)) ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (by omega) (by omega)
    have h33 : (2 * A + 1 + B) ^ 2 ≤ (4 * c * (M + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4M : 4 * M ≤ (4 * c * (M + 1)) ^ 2 :=
      (show 4 * M ≤ 4 * c * (M + 1) by omega).trans (Nat.le_self_pow two_ne_zero _)
    have hsq : (M + 1) ^ 2 ≤ 2 * (M ^ 2 + 1) := by nlinarith
    calc M + M + (A + 1) * (A + B + 1) + (M + M + (2 * A + 1 + B) ^ 2)
        ≤ 3 * (4 * c * (M + 1)) ^ 2 := by omega
      _ = 48 * c ^ 2 * (M + 1) ^ 2 := by ring
      _ ≤ 48 * c ^ 2 * (2 * (M ^ 2 + 1)) := Nat.mul_le_mul_left _ hsq
      _ = 96 * c ^ 2 * (M ^ 2 + 1) := by ring
  refine ((ComputableInO.or' (ComputableInO.eq' ha hb) (hedge.comp (ha.prod hb))).of_enc_eq
    (encC := encBool) fun _ => rfl).mono (96 * (ca + cb + 1) ^ 2) (fun p => ?_) fun p => ?_
  · have hA := hca p
    have hB := hcb p
    simp only [length_encPair, encBits_apply, hN] at hA hB ⊢
    exact hbd _ _ _ hA hB
  · have hA := hca p
    have hB := hcb p
    simp only [length_encPair, encBits_apply, hN] at hA hB ⊢
    have h := hbd _ _ _ hA hB
    generalize (p.2.2.1.getD (viewCode p.1 (ntm.initView p.2.1))).length = A at h ⊢
    generalize (p.2.2.2.getD (acceptCode p.1)).length = B at h ⊢
    have : 2 * A + 1 + B ≤ (A + 1) * (A + B + 1) := by nlinarith
    omega

end Turing.MultiTapeNTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Reachability

variable {α : Type} {enc : α ↪ List Bool}

/-- A midpoint chosen in the midpoint game on words of width `w`, as an encoded option, has at most
`w + 1` bits. -/
private theorem length_encOption_lastMidpoint_le (w i : ℕ) (z : List Bool) (d : Bool) :
    (encOption encBits (lastMidpoint w i z d)).length ≤ w + 1 := by
  induction i generalizing z with
  | zero => simp [lastMidpoint]
  | succ i ih =>
    have hi := ih (z.drop (2 * w + 2))
    simp only [lastMidpoint]
    rcases h : lastMidpoint w i (z.drop (2 * w + 2)) d with _ | m
    · split_ifs <;> simp [midpointMoves]
    · rw [h] at hi
      simpa using hi

/-- For a time-constructible `s` and a constant `K`, the number of moves of the midpoint game on
codes of `2 * w + 2` bits, `w = K * (n + s n + 1)`, as in `exists_midpointGame_of_mem_NSPACE`, is
written in unary within time and space `O((n + s n + 1) ^ 2)`. -/
private theorem computableInO_midpointMoveCount {s : ℕ → ℕ} (hs : TimeConstructible s) (K : ℕ) :
    ComputableInO (fun a : α =>
      2 * ((2 * (K * ((enc a).length + s (enc a).length + 1)) + 2 + 1) *
        (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2))) enc encUnary
      (fun a => ((enc a).length + s (enc a).length + 1) ^ 2)
      fun a => ((enc a).length + s (enc a).length + 1) ^ 2 := by
  have h := (hs.computableInO_unary_of_polyTime
    (by fun_prop : ComputableInPolyTime (fun p : ℕ × ℕ =>
      2 * ((2 * (K * (p.1 + p.2 + 1)) + 2 + 1) * (2 * (K * (p.1 + p.2 + 1)) + 2)))
      (encPair encNat encNat) encNat)).comp
    (ComputableInO.of_eq (f := fun a : α => enc a) (encMid := encBits) fun _ => rfl)
  exact (fun hb => h.mono (8 * K ^ 2 + 20 * K + 14) hb hb) fun a => by
    set m := (enc a).length + s (enc a).length + 1
    have hm2 : m ≤ m ^ 2 := Nat.le_self_pow two_ne_zero m
    have hKm : K * m ≤ K * m ^ 2 := Nat.mul_le_mul_left K hm2
    have e : 2 * ((2 * (K * m) + 2 + 1) * (2 * (K * m) + 2)) =
        8 * K ^ 2 * m ^ 2 + 20 * (K * m) + 12 := by ring
    have e2 : (8 * K ^ 2 + 20 * K + 14) * (m ^ 2 + 1) =
        8 * K ^ 2 * m ^ 2 + 20 * (K * m ^ 2) + 14 * m ^ 2 + (8 * K ^ 2 + 20 * K + 14) := by
      ring
    omega

/-- The reduction of `NSPACE s ⊆ ATIME ((n + s n) ^ 2)` to the leaf test: the alternating machine
plays Savitch's midpoint game on the views of a machine deciding the problem
(`Cslib.Complexity.exists_midpointGame_of_mem_NSPACE`), with the number of moves and the width
written in unary within time `O((n + s n + 1) ^ 2)`, both endpoints of the play extracted within
time linear in the number of moves (`Cslib.Reachability.computableInO_lastMidpoint`), and the leaf
test `hleaf` on codes of width linear in `n + s n` (`Cslib.Complexity.mem_ATIME_of_alternation`). -/
private theorem NSPACE_subset_ATIME_sq_of_midpointLeaf {s : ℕ → ℕ} (hs : TimeConstructible s)
    (hleaf : ∀ {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State),
      ComputableInO
        (fun ((w, input, u, v) : ℕ × List Bool × Option (List Bool) × Option (List Bool)) =>
          ntm.midpointLeaf w input u v)
        (encPair encUnary (encPair encBits (encPair (encOption encBits) (encOption encBits))))
        encBool
        (fun p => (encPair encUnary (encPair encBits (encPair (encOption encBits)
          (encOption encBits))) p).length ^ 2)
        fun p => (encPair encUnary (encPair encBits (encPair (encOption encBits)
          (encOption encBits))) p).length ^ 2) :
    NSPACE enc s ⊆ ATIME enc fun n => (n + s n) ^ 2 := by
  intro A h
  obtain ⟨k, State, hfin, ntm, K, hA⟩ := exists_midpointGame_of_mem_NSPACE h
  have henc : ComputableInO (fun x : α × List Bool => enc x.1) (encPair enc encBits) encBits
      (fun x => (encPair enc encBits x).length) (fun x => (encPair enc encBits x).length) :=
    (ComputableInO.of_eq (f := fun a : α => enc a) (encMid := encBits) fun _ => rfl).comp_linear
      (ComputableInO.fst enc encBits)
  have hW₁ := (hs.computableInO_unary_of_polyTime (by fun_prop : ComputableInPolyTime
    (fun p : ℕ × ℕ => K * (p.1 + p.2 + 1)) (encPair encNat encNat) encNat)).comp henc
  have hW₂ := (hs.computableInO_unary_of_polyTime (by fun_prop : ComputableInPolyTime
    (fun p : ℕ × ℕ => 2 * (K * (p.1 + p.2 + 1)) + 2) (encPair encNat encNat) encNat)).comp henc
  have hmid (d : Bool) := (computableInO_lastMidpoint d).comp
    (hW₂.prod (hW₂.prod (ComputableInO.snd enc encBits)))
  have hV' := (fun hb =>
    ((hleaf ntm).comp (hW₁.prod (henc.prod ((hmid true).prod (hmid false))))).mono
    (2 * (8 * K + 15) ^ 2 + 40 * K ^ 2 + 100 * K + 200)
    (T' := fun x => ((enc x.1).length + s (enc x.1).length + 1) ^ 2 + x.2.length)
    (S' := fun x => ((enc x.1).length + s (enc x.1).length + 1) ^ 2 + x.2.length) hb hb) fun x => by
    obtain ⟨a, z⟩ := x
    set m := (enc a).length + s (enc a).length + 1
    have h₁ := length_encOption_lastMidpoint_le (2 * (K * m) + 2) (2 * (K * m) + 2) z true
    have h₂ := length_encOption_lastMidpoint_le (2 * (K * m) + 2) (2 * (K * m) + 2) z false
    simp only [Function.comp_apply, length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply]
    generalize (encOption encBits (lastMidpoint _ _ z true)).length = e₁ at h₁ ⊢
    generalize (encOption encBits (lastMidpoint _ _ z false)).length = e₂ at h₂ ⊢
    generalize hW : K * m = W at h₁ h₂ ⊢
    have e₀ : (2 * (2 * W + 2) + 2) * (2 * W + 2) = 8 * (W * W) + 20 * W + 12 := by ring
    have hWW : W * W = K ^ 2 * m ^ 2 := by rw [← hW]; ring
    have hX2 := Nat.pow_le_pow_left (by
      have : (8 * K + 15) * m = 8 * W + 15 * m := by rw [← hW]; ring
      omega : 2 * W + 1 + (2 * (enc a).length + 1 + (2 * e₁ + 1 + e₂)) ≤ (8 * K + 15) * m) 2
    have e₃ : ((8 * K + 15) * m) ^ 2 = 64 * (K ^ 2 * m ^ 2) + 240 * (K * m ^ 2) + 225 * m ^ 2 := by
      ring
    have hm2 : m ≤ m ^ 2 := Nat.le_self_pow two_ne_zero m
    have hWm : W ≤ K * m ^ 2 := by rw [← hW]; exact Nat.mul_le_mul_left K hm2
    have e₄ : (2 * (8 * K + 15) ^ 2 + 40 * K ^ 2 + 100 * K + 200) * (m ^ 2 + z.length + 1) =
        168 * (K ^ 2 * m ^ 2) + 580 * (K * m ^ 2) + 650 * m ^ 2 +
          (2 * (8 * K + 15) ^ 2 + 40 * K ^ 2 + 100 * K + 200) * (z.length + 1) := by ring
    have hc : 200 * (z.length + 1) ≤
        (2 * (8 * K + 15) ^ 2 + 40 * K ^ 2 + 100 * K + 200) * (z.length + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hfin (a : α) :
      2 * ((2 * (K * ((enc a).length + s (enc a).length + 1)) + 2 + 1) *
        (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2)) +
        ((enc a).length + s (enc a).length + 1) ^ 2 + (enc a).length ≤
      (2 * (8 * K + 15) ^ 2 + 64 * K ^ 2 + 140 * K + 260) *
        ((enc a).length + s (enc a).length) ^ 2 +
        (2 * (8 * K + 15) ^ 2 + 64 * K ^ 2 + 140 * K + 260) := by
    set p := (enc a).length + s (enc a).length
    have hn : (enc a).length ≤ p := Nat.le_add_right _ _
    have hp : p ≤ p ^ 2 + 1 := (Nat.le_self_pow two_ne_zero p).trans (Nat.le_succ _)
    have hKp : K * p ≤ K * p ^ 2 + K := (Nat.mul_le_mul_left K hp).trans_eq (by ring)
    have hK2p : K ^ 2 * p ≤ K ^ 2 * p ^ 2 + K ^ 2 :=
      (Nat.mul_le_mul_left _ hp).trans_eq (by ring)
    have e1 : 2 * ((2 * (K * (p + 1)) + 2 + 1) * (2 * (K * (p + 1)) + 2)) + (p + 1) ^ 2 =
        8 * (K ^ 2 * p ^ 2) + 16 * (K ^ 2 * p) + 8 * K ^ 2 +
          20 * (K * p) + 20 * K + p ^ 2 + 2 * p + 13 := by ring
    have e2 : (2 * (8 * K + 15) ^ 2 + 64 * K ^ 2 + 140 * K + 260) * p ^ 2 +
          (2 * (8 * K + 15) ^ 2 + 64 * K ^ 2 + 140 * K + 260) =
        192 * (K ^ 2 * p ^ 2) + 192 * K ^ 2 + 620 * (K * p ^ 2) + 620 * K +
          710 * p ^ 2 + 710 := by ring
    omega
  refine mem_ATIME_of_alternation
    (C := 2 * (8 * K + 15) ^ 2 + 64 * K ^ 2 + 140 * K + 260)
    (computableInO_midpointMoveCount hs K) hV'
    (fun a => (hA a _ le_rfl).trans (Iff.of_eq (congrArg (Alternation true _)
      (funext fun z => by rw [midpointGame_eq_reach_lastMidpoint]; rfl))))
    (fun a => by
      dsimp only at *
      have := hfin a
      omega)
    fun a z hz => by
      dsimp only at *
      have := hfin a
      omega

/-- **Time-constructible step toward CKS Theorem 3.1 (`NSPACE s ⊆ ATIME ((n + s n) ^ 2)`)**: not
the unrestricted [Chandra, Kozen and Stockmeyer, Theorem 3.1][ChandraKozenStockmeyer1981]
(`NSPACE(S) ⊆ ⋃_{c > 0} ATIME(c * S ^ 2)` for `S(n) ≥ n` without constructibility, which remains
open in #4086), because it restricts `s` to `TimeConstructible s`. For a time-constructible `s`,
every problem in `NSPACE s` is in `ATIME ((n + s n) ^ 2)`: the alternating machine plays Savitch's
midpoint game on the views of a machine deciding the problem
(`Cslib.Complexity.exists_midpointGame_of_mem_NSPACE`), and its verifier, including the leaf test
(`Turing.MultiTapeNTM.computableInO_midpointLeaf`), runs within time `O((n + s n) ^ 2)`.

This statement differs from Theorem 3.1 in two ways: `s` is assumed time-constructible, to write
the number of moves of the game in unary (#4086); and the bound is Sipser's form `O((n + s n) ^ 2)`
for every `s`, which is `O(s n ^ 2)` under the hypothesis `s n ≥ n` of Theorem 3.1. Both classes
are relative to the encoding `enc` of instances. -/
theorem NSPACE_subset_ATIME_sq_of_timeConstructible {s : ℕ → ℕ} (hs : TimeConstructible s) :
    NSPACE enc s ⊆ ATIME enc fun n => (n + s n) ^ 2 :=
  NSPACE_subset_ATIME_sq_of_midpointLeaf hs fun ntm => ntm.computableInO_midpointLeaf

end Cslib.Complexity
