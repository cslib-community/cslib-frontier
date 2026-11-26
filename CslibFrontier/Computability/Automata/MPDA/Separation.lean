/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.Underapprox
public import Mathlib.Computability.Language
import CslibFrontier.Computability.Automata.MPDA.OneHole
import CslibFrontier.Foundations.Data.List.Extract
import CslibFrontier.Foundations.Data.List.Flatten

/-! # Hole-bounded languages that are not scope-bounded

The second sentence of Proposition 2 of [AkshayGastinKrishnaRoychowdhury2020] states that some
languages are `K`-hole-bounded for a constant `K` but not `K'`-round-, context- or scope-bounded for
any `K'`. The witness is the visibly pushdown language

  `L_bh = {aⁿ bⁿ (a^{p₁} c^{p₁+1} b^{q₁} d^{q₁+1}) ⋯ (a^{pₙ} c^{pₙ+1} b^{qₙ} d^{qₙ+1})}`,

where `a`, `b` push on stacks `0`, `1` and `c`, `d` pop from them. We prove both halves for every
MPDA that reads these letters visibly, that is, whose transitions on each letter perform an
operation of the kind the letter prescribes.

## Main definitions

- `MPDA.HoleSeparation.language`: the language `L_bh`.

## Main results

- `MPDA.HoleSeparation.holeBounded_two`: complete runs of a visibly MPDA on words of `L_bh` are
  `2`-hole-bounded.
- `MPDA.HoleSeparation.not_scopeBounded`: for every `K` and every `m` with `K < 2 * m`, complete
  runs of a visibly MPDA on `aᵐ bᵐ (c d)ᵐ ∈ L_bh` are not `K`-scope-bounded.
- `MPDA.HoleSeparation.exists_not_roundBounded`: hence for every `K`, `L_bh` has a word on which
  no run is `K`-scope-, context- or round-bounded.

These are the run-level steps. `MPDA.HoleSeparation.language_separates_holeBounded_scopeBounded` in
`SeparationAutomaton.lean` combines them with a finite visibly MPDA recognizing exactly `L_bh` into
the separation of languages.

## Implementation notes

The paper's argument is about the visible operation sequence of the words of `L_bh`, and this file
states the result for visibly MPDAs. Whether the separation holds when stack operations are hidden,
as in the acceptance condition of `MPDA`, is open (cslib-frontier issue #6712). The paper's witness
for unbounded scope is `aᵐ bᵐ (a c² b d²)ᵐ`; we use the simpler `aᵐ bᵐ (c d)ᵐ`, the words of `L_bh`
with `pᵢ = qᵢ = 0`, whose scope is likewise `2 * m`.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {State Γ α : Type*}

/-! ## Contexts of visibly read factors -/

/-- The stack an operation kind touches, if any. -/
private def OpKind.stack : OpKind n → Option (Fin n)
  | .nop => none
  | .push i => some i
  | .pop i => some i

private theorem Op.stack_eq_kind_stack (op : Op n Γ) : op.stack = op.kind.stack := by
  cases op <;> rfl

/-- A factor containing operations on two different stacks is not a context. -/
private theorem not_isContext_extract {w : List (α × Op n Γ)} {a b s₁ s₂ : ℕ} {μ₁ μ₂ : α × Op n Γ}
    {i j : Fin n} (hij : i ≠ j) (h₁ : a ≤ s₁ ∧ s₁ < b) (h₂ : a ≤ s₂ ∧ s₂ < b)
    (hμ₁ : w[s₁]? = some μ₁) (hμ₂ : w[s₂]? = some μ₂) (hs₁ : μ₁.2.stack = some i)
    (hs₂ : μ₂.2.stack = some j) : ¬IsContext (w.extract a b) := by
  rintro ⟨o, ho⟩
  rcases ho μ₁ (List.mem_extract_iff_getElem?.mpr ⟨s₁, h₁.1, h₁.2, hμ₁⟩) with h | h <;>
    rcases ho μ₂ (List.mem_extract_iff_getElem?.mpr ⟨s₂, h₂.1, h₂.2, hμ₂⟩) with h' | h' <;>
    simp_all

/-! ## The language `L_bh` -/

namespace HoleSeparation

/-- The letters of `L_bh`. -/
inductive Letter where
  | a | b | c | d
  deriving DecidableEq

/-- `a` and `b` push on stacks `0` and `1`, `c` and `d` pop from them. -/
@[expose] def kind : Letter → OpKind 2
  | .a => .push 0
  | .b => .push 1
  | .c => .pop 0
  | .d => .pop 1

/-- A group `aᵖ cᵖ⁺¹ b^q d^(q+1)`: a well-nested factor on each stack, each followed by one extra
pop. -/
@[expose] def group (p q : ℕ) : List Letter :=
  List.replicate p .a ++ List.replicate (p + 1) .c ++ List.replicate q .b ++
    List.replicate (q + 1) .d

/-- The language `L_bh = {aⁿ bⁿ G₁ ⋯ Gₙ}` of [AkshayGastinKrishnaRoychowdhury2020], where each `Gᵢ`
is a group. -/
@[expose] def language : Language Letter :=
  {w | ∃ (n : ℕ) (gs : List (List Letter)), gs.length = n ∧ (∀ g ∈ gs, ∃ p q, g = group p q) ∧
    w = List.replicate n .a ++ List.replicate n .b ++ gs.flatten}

variable {M : MPDA 2 State Letter Γ}

/-- A position of a sequence whose letter has a push kind is a push. -/
private theorem isPushOn_of_letter {w : List (Letter × Op 2 Γ)}
    (hw : ∀ μ ∈ w, μ.2.kind = kind μ.1) {t : ℕ} {x : Letter} {i : Fin 2}
    (ht : (w.map Prod.fst)[t]? = some x) (hx : kind x = .push i) : IsPushOn w i t := by
  rw [List.getElem?_map] at ht
  obtain ⟨μ, hμ, rfl⟩ := Option.map_eq_some_iff.mp ht
  obtain ⟨γ, hγ⟩ := Op.kind_eq_push.mp ((hw μ (List.mem_of_getElem? hμ)).trans hx)
  exact ⟨μ.1, γ, by rw [hμ, ← hγ]⟩

/-- A run reading `xᵖ yᵖ`, where `x` pushes on stack `i` and `y` pops from it, is well-nested. -/
private theorem wellNested_of_replicate {c c' : Config 2 State Γ} {v : List (Letter × Op 2 Γ)}
    (h : M.configLTS.MTr c v c') (hv : ∀ μ ∈ v, μ.2.kind = kind μ.1) {x y : Letter} {i : Fin 2}
    (hx : kind x = .push i) (hy : kind y = .pop i) {p : ℕ}
    (hvp : v.map Prod.fst = List.replicate p x ++ List.replicate p y) : WellNested v := by
  refine wellNested_of_not_crossing h (fun j => ⟨?_, fun k => ?_⟩) ?_
  · rw [net_eq_of_kind hv, hvp]
    simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate, hx, hy,
      OpKind.net]
    split_ifs <;> simp
  · rw [net_eq_of_kind (fun μ hμ => hv μ (List.mem_of_mem_take hμ)), List.map_take, hvp]
    simp only [List.take_append, List.take_replicate, List.map_append, List.map_replicate,
      List.sum_append, List.sum_replicate, List.length_replicate, hx, hy, OpKind.net]
    split_ifs <;> simp
  · rintro ⟨i₁, i₂, p₁, p₂, z, hne, -, -, ⟨a₁, γ₁, h₁⟩, ⟨a₂, γ₂, h₂⟩, -⟩
    have hstack {i' : Fin 2} {t : ℕ} {l : Letter} {γ : Γ}
        (ht : v[t]? = some (l, Op.push i' γ)) : i' = i := by
      have hk := hv _ (List.mem_of_getElem? ht)
      have hmem := hvp ▸ List.mem_map.mpr ⟨_, List.mem_of_getElem? ht, rfl⟩
      simp only [List.mem_append, List.mem_replicate] at hmem
      rcases hmem with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simpa [hx, Op.kind, eq_comm] using hk
      · simp [hy, Op.kind] at hk
    exact hne ((hstack h₁).trans (hstack h₂).symm)

/-- In a run, a push inside a factor reading `xᵖ yᵖ`, where `x` pushes on stack `i` and `y` pops
from it, is closed by a well-nested continuation. -/
private theorem wellMatched_of_replicate {c c' : Config 2 State Γ}
    {u v u' : List (Letter × Op 2 Γ)} (h : M.configLTS.MTr c (u ++ v ++ u') c')
    (hv : ∀ μ ∈ u ++ v ++ u', μ.2.kind = kind μ.1) {x y : Letter} {i : Fin 2}
    (hx : kind x = .push i) (hy : kind y = .pop i) {p : ℕ}
    (hvp : v.map Prod.fst = List.replicate p x ++ List.replicate p y) {k : ℕ} (hk : k < p) :
    WellMatched (u ++ v ++ u') (u.length + k) := by
  obtain ⟨c₁, -, h₁⟩ := LTS.MTr.split (List.append_assoc u v u' ▸ h)
  obtain ⟨c₂, hrun, -⟩ := LTS.MTr.split h₁
  have hv' : ∀ μ ∈ v, μ.2.kind = kind μ.1 := fun μ hμ => hv μ (by simp [hμ])
  refine WellMatched.append ((wellNested_of_replicate hrun hv' hx hy hvp).exists_wellMatched
    (isPushOn_of_letter hv' ?_ hx)) u u'
  rw [hvp, List.getElem?_append_left (by simpa using hk), List.getElem?_replicate_of_lt hk]

/-- In a run, every push inside a sequence of groups is closed by a well-nested continuation. -/
private theorem wellMatched_of_groups {c c' : Config 2 State Γ} :
    ∀ (gs : List (List Letter)), (∀ g ∈ gs, ∃ p q, g = group p q) →
      ∀ (u v u' : List (Letter × Op 2 Γ)), M.configLTS.MTr c (u ++ v ++ u') c' →
      (∀ μ ∈ u ++ v ++ u', μ.2.kind = kind μ.1) → v.map Prod.fst = gs.flatten →
      ∀ k < v.length, ∀ i, IsPushOn (u ++ v ++ u') i (u.length + k) →
        WellMatched (u ++ v ++ u') (u.length + k)
  | [], _, u, v, u', _, _, hv, k, hk, _, _ => by simp_all
  | g :: gs, hgs, u, v, u', h, hkind, hv, k, hk, i, hpush => by
    rw [List.flatten_cons] at hv
    obtain ⟨vg, vr, rfl, hvg, hvr⟩ := List.map_eq_append_iff.mp hv
    by_cases hkg : k < vg.length
    · obtain ⟨p, q, rfl⟩ := hgs g List.mem_cons_self
      -- The letter at the push.
      obtain ⟨a', γ', hpush'⟩ := hpush
      have hvgk : vg[k]? = some (a', .push i γ') := by
        rwa [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
          List.getElem?_append_left (by simp; omega), List.getElem?_append_left hkg] at hpush'
      have hkind' := hkind _ (List.mem_of_getElem? hpush')
      simp only [Op.kind] at hkind'
      have hsym : (group p q)[k]? = some a' := by rw [← hvg, List.getElem?_map, hvgk]; rfl
      -- Split the group into its four blocks.
      unfold group at hvg hsym
      obtain ⟨v₁, ld, rfl, hv₁, hld⟩ := List.map_eq_append_iff.mp hvg
      obtain ⟨v₂, lb, rfl, hv₂, hlb⟩ := List.map_eq_append_iff.mp hv₁
      obtain ⟨la, lc, rfl, hla, hlc⟩ := List.map_eq_append_iff.mp hv₂
      have hla' : la.length = p := by simpa using congrArg List.length hla
      have hlc' : lc.length = p + 1 := by simpa using congrArg List.length hlc
      by_cases hka : k < p
      · -- A push in `aᵖ`: it lies in the factor `aᵖ cᵖ`.
        have heq : u ++ (la ++ lc.take p) ++ (lc.drop p ++ lb ++ ld ++ vr ++ u') =
            u ++ (la ++ lc ++ lb ++ ld ++ vr) ++ u' := by
          conv_rhs => rw [← List.take_append_drop p lc]
          simp only [List.append_assoc]
        have := wellMatched_of_replicate (x := .a) (y := .c) (i := 0) (heq ▸ h) (heq ▸ hkind)
          rfl rfl (by rw [List.map_append, hla, List.map_take, hlc, List.take_replicate,
            min_eq_left (Nat.le_succ p)]) hka
        rwa [heq] at this
      by_cases hkc : k < p + (p + 1)
      · -- A letter `c` is a pop.
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
          List.getElem?_append_right (by simp; omega), List.getElem?_replicate] at hsym
        simp only [List.length_replicate, show k - p < p + 1 by omega, ite_true,
          Option.some.injEq] at hsym
        subst hsym
        simp [kind] at hkind'
      by_cases hkb : k < p + (p + 1) + q
      · -- A push in `b^q`: it lies in the factor `b^q d^q`.
        have heq : u ++ la ++ lc ++ (lb ++ ld.take q) ++ (ld.drop q ++ vr ++ u') =
            u ++ (la ++ lc ++ lb ++ ld ++ vr) ++ u' := by
          conv_rhs => rw [← List.take_append_drop q ld]
          simp only [List.append_assoc]
        have := wellMatched_of_replicate (x := .b) (y := .d) (i := 1) (heq ▸ h) (heq ▸ hkind)
          rfl rfl (by rw [List.map_append, hlb, List.map_take, hld, List.take_replicate,
            min_eq_left (Nat.le_succ q)]) (show k - (p + (p + 1)) < q by omega)
        rwa [heq, List.length_append, List.length_append, hla', hlc',
          show u.length + p + (p + 1) + (k - (p + (p + 1))) = u.length + k by omega] at this
      · -- A letter `d` is a pop.
        rw [List.getElem?_append_right (by simp; omega), List.getElem?_replicate] at hsym
        simp only [List.length_append, List.length_replicate, Option.ite_none_right_eq_some,
          Option.some.injEq] at hsym
        obtain ⟨-, rfl⟩ := hsym
        simp [kind] at hkind'
    · -- The push lies in a later group.
      have hk' : u.length + vg.length + (k - vg.length) = u.length + k := by omega
      have := wellMatched_of_groups gs (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
        (u ++ vg) vr u' (by simpa [List.append_assoc] using h)
        (by simpa [List.append_assoc] using hkind) hvr (k - vg.length) (by simp at hk; omega) i
        (by rw [List.length_append, hk']; simpa [List.append_assoc] using hpush)
      rw [List.length_append, hk'] at this
      simpa [List.append_assoc] using this

/-- **`L_bh` is `2`-hole-bounded**, the hole bound in the second sentence of Proposition 2 of
[AkshayGastinKrishnaRoychowdhury2020] (arXiv:2002.05950v2, Section 2.1, printed pp. 6-7): every
run of a visibly MPDA on a word of `L_bh` is `2`-hole-bounded. At each position, the only first
pending hole pushes can be the first `a` and the first `b`: pushes inside groups are closed by
well-nested continuations, and every other pending `a` or `b` belongs to the hole of the push
before it. -/
theorem holeBounded_two (hM : M.IsVisibly kind) {c c' : Config 2 State Γ}
    {w : List (Letter × Op 2 Γ)} (h : M.configLTS.MTr c w c') (hw : w.map Prod.fst ∈ language) :
    HoleBounded 2 w := by
  obtain ⟨n, gs, -, hgs, hwn⟩ := hw
  have hkind := hM.kind_eq h
  obtain ⟨wab, wg, rfl, hwab, hwg⟩ := List.map_eq_append_iff.mp hwn
  have hwab' : wab.length = n + n := by simpa using congrArg List.length hwab
  have hlet : ∀ t : ℕ, ((wab ++ wg).map Prod.fst)[t]? = (List.replicate n Letter.a ++
      List.replicate n Letter.b ++ gs.flatten)[t]? := fun t => by rw [hwn]
  intro x _
  have hsub : {q | OpenHolePush (wab ++ wg) x q ∧ ¬∃ p, SameHole (wab ++ wg) x p q} ⊆
      ({0, n} : Set ℕ) := by
    rintro q ⟨hq, hns⟩
    obtain ⟨⟨⟨i, hpush⟩, hnot⟩, -, hqx, -⟩ := id hq
    by_cases hq2 : n + n ≤ q
    · -- Pushes in the groups are closed by well-nested continuations.
      have hq' : wab.length + (q - wab.length) = q := by omega
      have := wellMatched_of_groups gs hgs wab wg [] (by simpa using h) (by simpa using hkind)
        hwg (q - wab.length) (by
          have := (List.getElem?_eq_some_iff.mp hpush.choose_spec.choose_spec).1
          simp at this; omega) i (by rw [hq']; simpa using hpush)
      rw [hq'] at this
      exact (hnot (by simpa using this)).elim
    · -- Every other pending `a` or `b` belongs to the hole of the push before it.
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra! hq0
      have hsame : ∀ (x' : Letter) (j : Fin 2), kind x' = .push j →
          (List.replicate n Letter.a ++ List.replicate n Letter.b ++ gs.flatten)[q - 1]? = some x' →
          (List.replicate n Letter.a ++ List.replicate n Letter.b ++ gs.flatten)[q]? = some x' →
          False := by
        intro x' j hx' h₁ h₂
        exact hns ⟨q - 1, OpenHolePush.sameHole_pred hq (by omega)
          (isPushOn_of_letter hkind (by rw [hlet, h₁]) hx')
          (isPushOn_of_letter hkind (by rw [hlet, h₂]) hx')⟩
      by_cases hqn : q < n
      · refine hsame .a 0 rfl ?_ ?_ <;> rw [List.append_assoc,
          List.getElem?_append_left (by simp; omega), List.getElem?_replicate_of_lt (by omega)]
      · refine hsame .b 1 rfl ?_ ?_ <;> rw [List.getElem?_append_left (by simp; omega),
          List.getElem?_append_right (by simp; omega),
          List.getElem?_replicate_of_lt (by simp; omega)]
  calc openHoles (wab ++ wg) x ≤ ({0, n} : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)

/-! ## Unbounded scope -/

/-- The word `aᵐ bᵐ (c d)ᵐ` of `L_bh`, with groups `c d`. -/
@[expose] def word (m : ℕ) : List Letter :=
  List.replicate m .a ++ List.replicate m .b ++ (List.replicate m [.c, .d]).flatten

theorem word_mem_language (m : ℕ) : word m ∈ language :=
  ⟨m, List.replicate m (group 0 0), by simp, by simp [List.mem_replicate], by
    simp [word, group]⟩

private theorem getElem?_flatten_cd (r j : ℕ) :
    (List.replicate r [Letter.c, .d]).flatten[j]? =
      if j < 2 * r then some (if j % 2 = 0 then .c else .d) else none := by
  rw [List.getElem?_flatten_replicate, List.length_cons, List.length_singleton,
    show r * (1 + 1) = 2 * r by omega]
  rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h]

private theorem length_word (m : ℕ) : (word m).length = 4 * m := by
  simp [word]; omega

/-- The net effect on stack `0` of a prefix of `(c d)ʳ`. -/
private theorem net_take_flatten_cd (r j : ℕ) :
    (((List.replicate r [Letter.c, .d]).flatten.take j).map fun l => (kind l).net 0).sum =
      -(min ((j + 1) / 2) r : ℕ) := by
  induction r generalizing j with
  | zero => simp
  | succ r ih =>
    rw [List.replicate_succ, List.flatten_cons]
    rcases j with _ | _ | j
    · simp
    · simp [kind, OpKind.net]
    · rw [List.take_append, List.take_of_length_le (by simp), show j + 2 - [Letter.c, .d].length = j
        by simp, List.map_append, List.sum_append, ih]
      simp [kind, OpKind.net]
      omega

/-- The net effect on stack `0` of a prefix of `aʳ bˢ (c d)ʳ`. -/
private theorem net_take_abcd (r s k : ℕ) :
    ((List.take k (List.replicate r Letter.a ++ List.replicate s .b ++
        (List.replicate r [Letter.c, .d]).flatten)).map fun l => (kind l).net 0).sum =
      ((min k r : ℕ) : ℤ) - ((min ((k - (r + s) + 1) / 2) r : ℕ) : ℤ) := by
  rw [List.take_append, List.map_append, List.sum_append, net_take_flatten_cd]
  simp only [List.take_append, List.take_replicate, List.map_append, List.map_replicate,
    List.sum_append, List.sum_replicate, List.length_append, List.length_replicate, kind,
    OpKind.net]
  simp; omega

/-- The factor of `word m` strictly between its first `a` and the last `c`. -/
private theorem extract_word (m : ℕ) (hm : 1 ≤ m) :
    (word m).extract 1 (4 * m - 2) =
      List.replicate (m - 1) .a ++ List.replicate m .b ++
        (List.replicate (m - 1) [Letter.c, .d]).flatten := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hw : word (m + 1) = Letter.a :: ((List.replicate m .a ++ List.replicate (m + 1) .b ++
      (List.replicate m [Letter.c, .d]).flatten) ++ [.c, .d]) := by
    simp [word, List.replicate_succ' (n := m) (a := [Letter.c, .d]), List.replicate_succ]
  rw [hw, List.extract_eq_take_drop, List.drop_succ_cons, List.drop_zero,
    List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp; omega)]
  simp

/-- Positions of `word m` alternating between the stacks: the first `a`, the first `b`, and then
the `c`s and `d`s. -/
private def altPos (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => m
  | k + 2 => 2 * m + k

/-- **`L_bh` has unbounded scope**, the scope half of the second sentence of Proposition 2 of
[AkshayGastinKrishnaRoychowdhury2020] (arXiv:2002.05950v2, Section 2.1, printed pp. 6-7): a run of a
visibly MPDA on `aᵐ bᵐ (c d)ᵐ` is not `K`-scope-bounded for `K < 2 * m`. The first `a` is popped by
the last `c`, and the `2 * m + 1` positions of the first `a`, the first `b` and every `c` and `d`
but the last `d` alternate between the two stacks, so they lie in pairwise distinct contexts. -/
theorem not_scopeBounded (hM : M.IsVisibly kind) {c c' : Config 2 State Γ}
    {w : List (Letter × Op 2 Γ)} (h : M.configLTS.MTr c w c') {m : ℕ}
    (hw : w.map Prod.fst = word m) {K : ℕ} (hK : K < 2 * m) : ¬ScopeBounded K w := by
  intro hs
  have hkind := hM.kind_eq h
  have hlen : w.length = 4 * m := by rw [← List.length_map (f := Prod.fst), hw, length_word]
  -- The letter at each position.
  have hpos {t : ℕ} {x : Letter} (ht : (word m)[t]? = some x) :
      ∃ μ, w[t]? = some μ ∧ μ.1 = x ∧ μ.2.kind = kind x := by
    rw [← hw, List.getElem?_map] at ht
    obtain ⟨μ, hμ, rfl⟩ := Option.map_eq_some_iff.mp ht
    exact ⟨μ, hμ, rfl, hkind μ (List.mem_of_getElem? hμ)⟩
  have hword_a (hm : 0 < m) : (word m)[0]? = some .a := by
    rw [word, List.append_assoc, List.getElem?_append_left (by simp; omega),
      List.getElem?_replicate_of_lt hm]
  have hword_cd {k : ℕ} (hk : k < 2 * m) :
      (word m)[2 * m + k]? = some (if k % 2 = 0 then .c else .d) := by
    rw [word, List.getElem?_append_right (by simp; omega), getElem?_flatten_cd]
    simp only [List.length_append, List.length_replicate,
      show 2 * m + k - (m + m) = k by omega, hk, ↓reduceIte]
  -- The first `a` matches the last `c`.
  have hmatch : Matches w 0 (4 * m - 2) := by
    obtain ⟨μa, hμa, -, hka⟩ := hpos (hword_a (by omega))
    obtain ⟨μc, hμc, -, hkc⟩ := hpos (t := 4 * m - 2) (x := .c) (by
      simpa [show 4 * m - 2 = 2 * m + (2 * m - 2) by omega,
        show (2 * m - 2) % 2 = 0 by omega] using hword_cd (k := 2 * m - 2) (by omega))
    obtain ⟨γa, hγa⟩ := Op.kind_eq_push.mp hka
    obtain ⟨γc, hγc⟩ : ∃ γ, μc.2 = .pop 0 γ := by
      rcases hop : μc.2 with _ | ⟨i, γ⟩ | ⟨i, γ⟩ <;> rw [hop] at hkc <;> simp_all [Op.kind, kind]
    have hsub : ∀ μ ∈ w.extract 1 (4 * m - 2), μ.2.kind = kind μ.1 := fun μ hμ =>
      hkind μ ((List.extract_isInfix w _ _).subset hμ)
    have hfst : (w.extract 1 (4 * m - 2)).map Prod.fst =
        List.replicate (m - 1) .a ++ List.replicate m .b ++
          (List.replicate (m - 1) [Letter.c, .d]).flatten := by
      rw [List.extract_eq_take_drop, List.map_take, List.map_drop, hw, ← List.extract_eq_take_drop,
        extract_word m (by omega)]
    refine ⟨by omega, 0, ⟨μa.1, γa, by rw [hμa, ← hγa]⟩, ⟨μc.1, γc, by rw [hμc, ← hγc]⟩,
      fun k => ?_, ?_⟩
    · rw [net_eq_of_kind (fun μ hμ => hsub μ (List.mem_of_mem_take hμ)), List.map_take, hfst,
        net_take_abcd]
      omega
    · rw [net_eq_of_kind hsub, hfst, ← List.take_of_length_le
        (l := List.replicate (m - 1) Letter.a ++ List.replicate m Letter.b ++
          (List.replicate (m - 1) [Letter.c, .d]).flatten)
        (show _ ≤ 4 * m by simp; omega), net_take_abcd]
      omega
  -- Positions alternating between the stacks: the first `a`, the first `b`, and the `c`s and
  -- `d`s up to the last `c`.
  have hf : StrictMono (altPos m) := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    rcases k with _ | _ | k <;> simp [altPos] <;> omega
  have hfstack : ∀ k < 2 * m + 1, ∃ μ, w[altPos m k]? = some μ ∧
      μ.2.stack = some (⟨k % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) := by
    intro k hk
    obtain ⟨x, hx, hxs⟩ : ∃ x, (word m)[altPos m k]? = some x ∧
        (kind x).stack = some (⟨k % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) := by
      rcases k with _ | _ | k
      · exact ⟨.a, hword_a (by omega), rfl⟩
      · refine ⟨.b, ?_, rfl⟩
        change (word m)[m]? = some .b
        rw [word, List.getElem?_append_left (by simp; omega),
          List.getElem?_append_right (by simp), List.getElem?_replicate_of_lt (by simp; omega)]
      · refine ⟨if k % 2 = 0 then .c else .d, hword_cd (by omega), ?_⟩
        rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2 <;>
          simp [hk2, kind, OpKind.stack, Nat.add_mod]
    obtain ⟨μ, hμ, -, hμk⟩ := hpos hx
    exact ⟨μ, hμ, by rw [Op.stack_eq_kind_stack, hμk, hxs]⟩
  -- The scope bound gives at most `K + 1` contexts from the first `a` to the last `c`.
  have hcb := hs 0 (4 * m - 2) hmatch
  rw [show 4 * m - 2 + 1 = 4 * m - 1 by omega] at hcb
  have hcard := List.Splits.card_le (fun _ _ huv hv => IsContext.of_isInfix huv hv) hcb
    ((Finset.range (2 * m + 1)).image (altPos m)) (by
      intro t ht
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
      have := Finset.mem_range.mp hk
      rw [List.extract_eq_take_drop, List.drop_zero, List.length_take, hlen]
      rcases k with _ | _ | k <;> simp [altPos] <;> omega) (by
      intro t ht t' ht' htt'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp ht'
      rw [Finset.mem_range] at hk hk'
      have hkk : k < k' := hf.lt_iff_lt.mp htt'
      have hmax : altPos m k' ≤ 4 * m - 2 := by
        rcases k' with _ | _ | k' <;> simp [altPos] <;> omega
      have hle : altPos m (k + 1) ≤ altPos m k' := hf.monotone hkk
      rw [List.extract_extract _ (by omega), Nat.zero_add, Nat.zero_add]
      obtain ⟨μ₁, hμ₁, hs₁⟩ := hfstack k (by omega)
      obtain ⟨μ₂, hμ₂, hs₂⟩ := hfstack (k + 1) (by omega)
      exact not_isContext_extract (i := ⟨k % 2, Nat.mod_lt _ (by omega)⟩)
        (j := ⟨(k + 1) % 2, Nat.mod_lt _ (by omega)⟩) (by simp [Fin.ext_iff]; omega)
        (s₂ := altPos m (k + 1)) ⟨le_rfl, by omega⟩ ⟨hf.monotone (Nat.le_succ k), by omega⟩
        hμ₁ hμ₂ hs₁ hs₂)
  rw [Finset.card_image_of_injective _ hf.injective, Finset.card_range] at hcard
  omega

/-- For every `K`, `L_bh` has a word on which no run of a visibly MPDA is `K`-scope-, `K`-context-
or `K`-round-bounded. This is the run-level step of the second sentence of Proposition 2 of
[AkshayGastinKrishnaRoychowdhury2020]; the separation of languages is
`MPDA.HoleSeparation.language_separates_holeBounded_scopeBounded`, which also shows that a finite
visibly MPDA recognizes exactly `L_bh`. -/
theorem exists_not_roundBounded (hM : M.IsVisibly kind) (K : ℕ) :
    ∃ v ∈ language, ∀ {c c' : Config 2 State Γ} {w : List (Letter × Op 2 Γ)},
      M.configLTS.MTr c w c' → w.map Prod.fst = v →
        ¬ScopeBounded K w ∧ ¬ContextBounded K w ∧ ¬RoundBounded K w := by
  refine ⟨word (K + 1), word_mem_language _, fun h hw => ⟨?_, ?_, ?_⟩⟩
  · exact not_scopeBounded hM h hw (by omega)
  · exact fun hc => not_scopeBounded hM h hw (by omega) hc.scopeBounded
  · exact fun hr => not_scopeBounded hM h hw (by omega) hr.contextBounded.scopeBounded

end HoleSeparation

end Cslib.Automata.MPDA
