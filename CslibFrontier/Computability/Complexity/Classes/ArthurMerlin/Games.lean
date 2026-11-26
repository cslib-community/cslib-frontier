/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Public-coin Arthur–Merlin games with a fixed pattern of moves

The Arthur–Merlin games of [Babai][Babai1985] and [Babai and Moran][BabaiMoran1988]
[Arora and Barak, Section 8.2][AroraBarak09] with any fixed pattern of moves. A move is
`AMMove.arthur` (Arthur sends fresh random bits) or `AMMove.merlin` (Merlin sends a message). A
*shape* `List (AMMove × ℕ)` lists the moves with their lengths, and a polynomial shape
`List (AMMove × Polynomial ℕ)` evaluates to a shape at the length `n` of the encoded instance
(`Cslib.Complexity.AMGame.evalShape`). The verifier reads the whole transcript, the messages
concatenated in order.

The value of a game is counted exactly, as for `MA` and `AM` (`Cslib.Complexity.MA`,
`Cslib.Complexity.AM`). `Cslib.Complexity.AMGame.count` sums over Arthur's random strings and takes
the maximum over Merlin's messages. Divided by `2 ^ B`, where `B` is the number of Arthur's bits
(`Cslib.Complexity.AMGame.arthurBits`), it is the acceptance probability against an optimal
Merlin. A problem `A` is in `AMGameClass enc π` when some polynomial shape with move pattern `π` and
some polynomial-time verifier have count at least two thirds of `2 ^ B` on members and at most one
third on non-members (`Cslib.Complexity.IsAMGameVerifier`). The alternating patterns give `AM[k]`
and `MA[k]` (`Cslib.Complexity.AMk`, `Cslib.Complexity.MAk`).

The proofs work with the normalised value `Cslib.Complexity.AMGame.value`, in `ℚ`, of a game on a
payoff `List Bool → ℚ`. Merlin maximises (`b = true`) or minimises (`b = false`). The value is
monotone and commutes with nonnegative affine maps, and it composes over concatenated shapes.
The two choices of `b` are dual (`Cslib.Complexity.AMGame.value_one_sub`).

## Main definitions

* `Cslib.Complexity.AMMove`, `Cslib.Complexity.alternatingMoves`.
* `Cslib.Complexity.AMGame.count`, `Cslib.Complexity.AMGame.arthurBits`,
  `Cslib.Complexity.AMGame.value`, `Cslib.Complexity.AMGame.evalShape`.
* `Cslib.Complexity.IsAMGameVerifier`, `Cslib.Complexity.AMGameClass`.
* `Cslib.Complexity.AMk`, `Cslib.Complexity.MAk`: `AM[k]` and `MA[k]`.

## Main results

* `Cslib.Complexity.AMGame.count_eq`: the count is `2 ^ B` times the value.
* `Cslib.Complexity.AMGameClass_nil`, `Cslib.Complexity.AMGameClass_arthur`,
  `Cslib.Complexity.AMGameClass_merlin`: the patterns `[]`, `A`, `M` give `P`, `BPP`, `NP`
  (`Cslib.Complexity.AMk_zero`, `Cslib.Complexity.MAk_zero`, `Cslib.Complexity.AMk_one`,
  `Cslib.Complexity.MAk_one`).
* `Cslib.Complexity.AMGameClass_arthur_merlin`: the pattern `A M` gives `AM`
  (`Cslib.Complexity.AMk_two`).
* `Cslib.Complexity.AMGameClass_merlin_arthur`: the pattern `M A` gives `MA`
  (`Cslib.Complexity.MAk_two`).
* `Cslib.Complexity.mem_AMGameClass_cons_merlin`: existential quantification over polynomially long
  words prepends a Merlin move.
* `Cslib.Complexity.AMGameClass_insert`, `Cslib.Complexity.AMGameClass_merge`,
  `Cslib.Complexity.AMGameClass_mono`: inserting a move, or merging two consecutive moves of the
  same player, does not shrink the class. So game classes are monotone along sublists of patterns.

The round collapse `AM[k] = AM` is in
`CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.RoundCollapse`, and parallel repetition
and error reduction in
`CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games.Repetition`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [L. Babai, *Trading group theory for randomness*][Babai1985]
* [L. Babai, S. Moran, *Arthur–Merlin games: a randomized proof system, and a hierarchy of
  complexity classes*][BabaiMoran1988]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type}

/-- A move of a public-coin Arthur–Merlin game. -/
inductive AMMove where
  /-- Arthur sends fresh random bits. -/
  | arthur
  /-- Merlin sends a message. -/
  | merlin
  deriving DecidableEq, Repr

/-- The other player. -/
def AMMove.other : AMMove → AMMove
  | .arthur => .merlin
  | .merlin => .arthur

/-- The alternating move pattern of length `k` starting with `x`. -/
def alternatingMoves : AMMove → ℕ → List AMMove
  | _, 0 => []
  | x, k + 1 => x :: alternatingMoves x.other k

namespace AMGame

/-- The count of a game shape `g` with verifier `V` on transcripts: the number of Arthur's random
strings that an optimal Merlin makes `V` accept. At an Arthur move of `n` bits it sums over the
`2 ^ n` coin strings, and at a Merlin move of `n` bits it takes the maximum over his `2 ^ n`
messages. Each message is prepended to the rest of the transcript, so Merlin's later messages may
depend on all earlier coins. -/
def count : List (AMMove × ℕ) → (List Bool → Bool) → ℕ
  | [], V => (V []).toNat
  | (.arthur, n) :: g, V => ∑ r : Fin n → Bool, count g fun t => V (List.ofFn r ++ t)
  | (.merlin, n) :: g, V => univ.sup fun y : Fin n → Bool => count g fun t => V (List.ofFn y ++ t)

/-- The number of Arthur's random bits in a game shape. -/
def arthurBits : List (AMMove × ℕ) → ℕ
  | [] => 0
  | (.arthur, n) :: g => n + arthurBits g
  | (.merlin, _) :: g => arthurBits g

/-- The value of a game shape `g` on a payoff `f`, normalised to a probability. Arthur's moves
average over their coins, and Merlin's moves take the maximum over his messages (`b = true`) or the
minimum (`b = false`). With `b = true` and a `0`/`1` payoff it is the count divided by
`2 ^ arthurBits g` (`Cslib.Complexity.AMGame.count_eq`). -/
def value (b : Bool) : List (AMMove × ℕ) → (List Bool → ℚ) → ℚ
  | [], f => f []
  | (.arthur, n) :: g, f => (∑ r : Fin n → Bool, value b g fun t => f (List.ofFn r ++ t)) / 2 ^ n
  | (.merlin, n) :: g, f => if b then
      univ.sup' univ_nonempty fun y : Fin n → Bool => value b g fun t => f (List.ofFn y ++ t)
    else univ.inf' univ_nonempty fun y : Fin n → Bool => value b g fun t => f (List.ofFn y ++ t)

theorem value_nil (b : Bool) (f : List Bool → ℚ) : value b [] f = f [] := rfl

theorem value_arthur (b : Bool) (n : ℕ) (g : List (AMMove × ℕ)) (f : List Bool → ℚ) :
    value b ((.arthur, n) :: g) f =
      (∑ r : Fin n → Bool, value b g fun t => f (List.ofFn r ++ t)) / 2 ^ n := rfl

theorem value_merlin_true (n : ℕ) (g : List (AMMove × ℕ)) (f : List Bool → ℚ) :
    value true ((.merlin, n) :: g) f =
      univ.sup' univ_nonempty fun y : Fin n → Bool => value true g fun t => f (List.ofFn y ++ t) :=
  rfl

theorem value_merlin_false (n : ℕ) (g : List (AMMove × ℕ)) (f : List Bool → ℚ) :
    value false ((.merlin, n) :: g) f =
      univ.inf' univ_nonempty fun y : Fin n → Bool => value false g fun t => f (List.ofFn y ++ t) :=
  rfl

/-- Total length of a transcript of a game. -/
def transcriptLength (g : List (AMMove × ℕ)) : ℕ := (g.map Prod.snd).sum

theorem value_mono_of_length (b : Bool) (g : List (AMMove × ℕ)) {f f' : List Bool → ℚ}
    (h : ∀ t : List Bool, t.length = transcriptLength g → f t ≤ f' t) :
    value b g f ≤ value b g f' := by
  induction g generalizing f f' with
  | nil => exact h [] rfl
  | cons x g ih =>
    obtain ⟨mv, n⟩ := x
    have hstep (r : Fin n → Bool) : (value b g fun t => f (List.ofFn r ++ t)) ≤
        value b g fun t => f' (List.ofFn r ++ t) :=
      ih fun t ht => h _ (by simp [transcriptLength, ht])
    cases mv
    · exact div_le_div_of_nonneg_right (sum_le_sum fun r _ => hstep r) (by positivity)
    · cases b
      · exact le_inf' univ_nonempty _ fun y _ => (inf'_le _ (mem_univ y)).trans (hstep y)
      · exact sup'_le univ_nonempty _ fun y _ => (hstep y).trans
          (le_sup' (fun y => value true g fun t => f' (List.ofFn y ++ t)) (mem_univ y))

theorem value_mono (b : Bool) (g : List (AMMove × ℕ)) {f f' : List Bool → ℚ}
    (h : ∀ t, f t ≤ f' t) : value b g f ≤ value b g f' :=
  value_mono_of_length b g fun t _ => h t

theorem value_congr_of_length (b : Bool) (g : List (AMMove × ℕ)) {f f' : List Bool → ℚ}
    (h : ∀ t : List Bool, t.length = transcriptLength g → f t = f' t) :
    value b g f = value b g f' :=
  le_antisymm (value_mono_of_length b g fun t ht => (h t ht).le)
    (value_mono_of_length b g fun t ht => (h t ht).ge)

/-- Values commute with nonnegative affine maps. -/
theorem value_affine (b : Bool) (g : List (AMMove × ℕ)) (f : List Bool → ℚ) {c : ℚ} (hc : 0 ≤ c)
    (d : ℚ) : value b g (fun t => c * f t + d) = c * value b g f + d := by
  induction g generalizing f with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp only [value_arthur, ih, sum_add_distrib, ← mul_sum, sum_const, card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      push_cast; ring
    · have hm : Monotone fun x : ℚ => c * x + d := fun _ _ hxy =>
        add_le_add (mul_le_mul_of_nonneg_left hxy hc) le_rfl
      cases b
      · simp only [value_merlin_false, ih]
        exact (Finset.apply_inf'_eq_inf'_comp _ (fun x : ℚ => c * x + d) fun _ _ => hm.map_min).symm
      · simp only [value_merlin_true, ih]
        exact (Finset.apply_sup'_eq_sup'_comp _ (fun x : ℚ => c * x + d) fun _ _ => hm.map_max).symm

theorem value_const (b : Bool) (g : List (AMMove × ℕ)) (d : ℚ) : value b g (fun _ => d) = d := by
  simpa using value_affine b g (fun _ => 0) le_rfl d

theorem value_const_add (b : Bool) (g : List (AMMove × ℕ)) (f : List Bool → ℚ) (d : ℚ) :
    value b g (fun t => d + f t) = d + value b g f := by
  simpa only [one_mul, add_comm] using value_affine b g f zero_le_one d

theorem value_nonneg (b : Bool) (g : List (AMMove × ℕ)) {f : List Bool → ℚ} (hf : ∀ t, 0 ≤ f t) :
    0 ≤ value b g f :=
  (value_const b g 0).symm.le.trans (value_mono b g hf)

theorem value_le_one (b : Bool) (g : List (AMMove × ℕ)) {f : List Bool → ℚ} (hf : ∀ t, f t ≤ 1) :
    value b g f ≤ 1 :=
  (value_mono b g hf).trans (value_const b g 1).le

/-- Values of a concatenated game. -/
theorem value_append (b : Bool) (g h : List (AMMove × ℕ)) (f : List Bool → ℚ) :
    value b (g ++ h) f = value b g fun s => value b h fun t => f (s ++ t) := by
  induction g generalizing f with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp only [List.cons_append, value_arthur, ih, List.append_assoc]
    · cases b <;>
        simp only [List.cons_append, value_merlin_false, value_merlin_true, ih, List.append_assoc]

private theorem one_sub_inf' {ι : Type} [Fintype ι] [Nonempty ι] (φ : ι → ℚ) :
    1 - univ.inf' univ_nonempty φ = univ.sup' univ_nonempty fun y => 1 - φ y := by
  obtain ⟨i, _, hi⟩ := exists_mem_eq_inf' univ_nonempty φ
  exact le_antisymm (hi ▸ le_sup' (fun y => 1 - φ y) (mem_univ i))
    (sup'_le _ _ fun y _ => sub_le_sub_left (inf'_le φ (mem_univ y)) 1)

private theorem one_sub_sup' {ι : Type} [Fintype ι] [Nonempty ι] (φ : ι → ℚ) :
    1 - univ.sup' univ_nonempty φ = univ.inf' univ_nonempty fun y => 1 - φ y := by
  obtain ⟨i, _, hi⟩ := exists_mem_eq_sup' univ_nonempty φ
  exact le_antisymm (le_inf' _ _ fun y _ => sub_le_sub_left (le_sup' φ (mem_univ y)) 1)
    (hi ▸ inf'_le (fun y => 1 - φ y) (mem_univ i))

/-- Duality between Merlin maximising and minimising. -/
theorem value_one_sub (b : Bool) (g : List (AMMove × ℕ)) (f : List Bool → ℚ) :
    value b g (fun t => 1 - f t) = 1 - value (!b) g f := by
  induction g generalizing f with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp only [value_arthur, ih, sum_sub_distrib, sum_const, card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      push_cast; ring
    · cases b <;> simp only [value_merlin_false, value_merlin_true, Bool.not_false,
        Bool.not_true, ih]
      · exact (one_sub_sup' _).symm
      · exact (one_sub_inf' _).symm

theorem value_merge_arthur (b : Bool) (σ τ : List (AMMove × ℕ)) (n₁ n₂ : ℕ)
    (f : List Bool → ℚ) :
    value b (σ ++ (.arthur, n₁) :: (.arthur, n₂) :: τ) f =
      value b (σ ++ (.arthur, n₁ + n₂) :: τ) f := by
  rw [value_append, value_append]
  congr 1 with s : 1
  simp only [value_arthur]
  have hsum : (∑ r : Fin (n₁ + n₂) → Bool, value b τ fun t => f (s ++ (List.ofFn r ++ t))) =
      ∑ r₁ : Fin n₁ → Bool, ∑ r₂ : Fin n₂ → Bool,
        value b τ fun t => f (s ++ (List.ofFn r₁ ++ (List.ofFn r₂ ++ t))) := by
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv (Fin.appendEquiv n₁ n₂) _ _ fun p => by
      simp [Fin.appendEquiv, List.ofFn_fin_append]).symm
  rw [hsum, pow_add]
  simp only [div_eq_mul_inv, sum_mul, mul_inv]
  refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem value_merge_merlin (σ τ : List (AMMove × ℕ)) (n₁ n₂ : ℕ) (f : List Bool → ℚ) :
    value true (σ ++ (.merlin, n₁) :: (.merlin, n₂) :: τ) f =
      value true (σ ++ (.merlin, n₁ + n₂) :: τ) f := by
  rw [value_append, value_append]
  congr 1 with s : 1
  simp only [value_merlin_true]
  refine le_antisymm (sup'_le _ _ fun y₁ _ => sup'_le _ _ fun y₂ _ => ?_)
    (sup'_le _ _ fun y _ => ?_)
  · have := le_sup' (fun y : Fin (n₁ + n₂) → Bool =>
      value true τ fun t => f (s ++ (List.ofFn y ++ t))) (mem_univ (Fin.append y₁ y₂))
    simpa only [List.ofFn_fin_append, List.append_assoc] using this
  · obtain ⟨⟨y₁, y₂⟩, rfl⟩ := (Fin.appendEquiv n₁ n₂).surjective y
    refine le_trans ?_ ((le_sup' (fun y₂ : Fin n₂ → Bool =>
      value true τ fun t => f (s ++ (List.ofFn y₁ ++ (List.ofFn y₂ ++ t)))) (mem_univ y₂)).trans
      (le_sup' (fun y₁ : Fin n₁ → Bool => univ.sup' univ_nonempty fun y₂ : Fin n₂ → Bool =>
        value true τ fun t => f (s ++ (List.ofFn y₁ ++ (List.ofFn y₂ ++ t)))) (mem_univ y₁)))
    simp [Fin.appendEquiv, List.ofFn_fin_append]

theorem value_insert_zero (b : Bool) (σ τ : List (AMMove × ℕ)) (x : AMMove) (f : List Bool → ℚ) :
    value b (σ ++ (x, 0) :: τ) f = value b (σ ++ τ) f := by
  rw [value_append, value_append]
  congr 1 with s : 1
  cases x
  · simp [value_arthur]
  · cases b
    · simpa only [value_merlin_false, List.ofFn_zero, List.nil_append] using inf'_const _ _
    · simpa only [value_merlin_true, List.ofFn_zero, List.nil_append] using sup'_const _ _

theorem count_eq (g : List (AMMove × ℕ)) (V : List Bool → Bool) :
    (count g V : ℚ) = 2 ^ arthurBits g * value true g (fun t => ((V t).toNat : ℚ)) := by
  induction g generalizing V with
  | nil => simp [count, arthurBits, value_nil]
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp only [count, arthurBits, value_arthur, Nat.cast_sum, ih, ← mul_sum, pow_add]
      field_simp
    · rw [count, arthurBits, value_merlin_true, ← sup'_eq_sup univ_nonempty,
        Finset.apply_sup'_eq_sup'_comp univ_nonempty (Nat.cast : ℕ → ℚ) Nat.cast_max,
        Finset.apply_sup'_eq_sup'_comp univ_nonempty _
          fun x y => mul_max_of_nonneg x y (by positivity)]
      exact sup'_congr univ_nonempty rfl fun y _ => ih _

theorem count_nil (V : List Bool → Bool) : count [] V = (V []).toNat := rfl

theorem count_arthur (n : ℕ) (g : List (AMMove × ℕ)) (V : List Bool → Bool) :
    count ((.arthur, n) :: g) V =
      ∑ r : Fin n → Bool, count g fun t => V (List.ofFn r ++ t) := rfl

theorem count_merlin (n : ℕ) (g : List (AMMove × ℕ)) (V : List Bool → Bool) :
    count ((.merlin, n) :: g) V =
      univ.sup fun y : Fin n → Bool => count g fun t => V (List.ofFn y ++ t) := rfl

theorem count_le_two_pow (g : List (AMMove × ℕ)) (V : List Bool → Bool) :
    count g V ≤ 2 ^ arthurBits g := by
  have hv : value true g (fun t => ((V t).toNat : ℚ)) ≤ 1 :=
    value_le_one _ _ fun t => by cases V t <;> norm_num
  exact_mod_cast (count_eq g V).trans_le (mul_le_of_le_one_right (by positivity) hv)

/-- Evaluate the move lengths of a polynomial game shape at `n`. -/
def evalShape (G : List (AMMove × Polynomial ℕ)) (n : ℕ) : List (AMMove × ℕ) :=
  G.map fun x => (x.1, x.2.eval n)

theorem evalShape_append (G H : List (AMMove × Polynomial ℕ)) (n : ℕ) :
    evalShape (G ++ H) n = evalShape G n ++ evalShape H n := by
  simp [evalShape]

theorem evalShape_cons (x : AMMove × Polynomial ℕ) (G : List (AMMove × Polynomial ℕ)) (n : ℕ) :
    evalShape (x :: G) n = (x.1, x.2.eval n) :: evalShape G n := rfl

/-- Total transcript length of a polynomial game shape. -/
noncomputable def transcriptLengthPoly (G : List (AMMove × Polynomial ℕ)) : Polynomial ℕ :=
  (G.map Prod.snd).sum

theorem transcriptLength_evalShape (G : List (AMMove × Polynomial ℕ)) (n : ℕ) :
    transcriptLength (evalShape G n) = (transcriptLengthPoly G).eval n := by
  induction G with
  | nil => simp [transcriptLength, transcriptLengthPoly, evalShape]
  | cons x G ih =>
    simp only [transcriptLength, transcriptLengthPoly, evalShape, List.map_cons, List.sum_cons,
      Polynomial.eval_add] at ih ⊢
    rw [ih]

end AMGame

open AMGame

/-- `V` is a game verifier for `A` with the polynomial shape `G`, evaluated at the length `n` of
the encoded instance: on a member an optimal Merlin makes `V (a, t)` accept for at least two thirds
of Arthur's random strings, and on a non-member for at most one third of them, whatever Merlin
sends. -/
def IsAMGameVerifier (enc : α ↪ List Bool) (G : List (AMMove × Polynomial ℕ))
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 * 2 ^ arthurBits (evalShape G (enc a).length) ≤
      3 * count (evalShape G (enc a).length) fun t => V (a, t)) ∧
    (a ∉ A → 3 * count (evalShape G (enc a).length) (fun t => V (a, t)) ≤
      2 ^ arthurBits (evalShape G (enc a).length))

/-- The problems with polynomial-time public-coin game verifiers whose moves follow the pattern
`π`, with polynomially long messages, with respect to the encoding `enc` of instances
[Babai and Moran][BabaiMoran1988]. -/
def AMGameClass (enc : α ↪ List Bool) (π : List AMMove) : Set (Set α) :=
  {A | ∃ (G : List (AMMove × Polynomial ℕ)) (V : α × List Bool → Bool),
    G.map Prod.fst = π ∧ ComputableInPolyTime V (encPair enc encBits) encBool ∧
      IsAMGameVerifier enc G V A}

/-- `AM[k]`: `k` alternating moves, Arthur first. -/
def AMk (enc : α ↪ List Bool) (k : ℕ) : Set (Set α) := AMGameClass enc (alternatingMoves .arthur k)

/-- `MA[k]`: `k` alternating moves, Merlin first. -/
def MAk (enc : α ↪ List Bool) (k : ℕ) : Set (Set α) := AMGameClass enc (alternatingMoves .merlin k)

theorem isAMGameVerifier_iff_value {enc : α ↪ List Bool} {G : List (AMMove × Polynomial ℕ)}
    {V : α × List Bool → Bool} {A : Set α} :
    IsAMGameVerifier enc G V A ↔ ∀ a,
      (a ∈ A → 2 ≤ 3 * value true (evalShape G (enc a).length)
        (fun t => ((V (a, t)).toNat : ℚ))) ∧
      (a ∉ A → 3 * value true (evalShape G (enc a).length)
        (fun t => ((V (a, t)).toNat : ℚ)) ≤ 1) := by
  refine forall_congr' fun a => ?_
  have hpos : (0 : ℚ) < 2 ^ arthurBits (evalShape G (enc a).length) := by positivity
  refine and_congr (imp_congr_right fun _ => ?_) (imp_congr_right fun _ => ?_)
  · rw [← Nat.cast_le (α := ℚ)]
    push_cast
    rw [count_eq, mul_comm (2 : ℚ), mul_left_comm (3 : ℚ), mul_le_mul_iff_right₀ hpos]
  · rw [← Nat.cast_le (α := ℚ)]
    push_cast
    rw [count_eq, mul_left_comm (3 : ℚ), mul_le_iff_le_one_right hpos]

theorem AMGameClass_insert {enc : α ↪ List Bool} (σ τ : List AMMove) (x : AMMove) :
    AMGameClass enc (σ ++ τ) ⊆ AMGameClass enc (σ ++ x :: τ) := by
  rintro A ⟨G, V, hG, hV, hA⟩
  obtain ⟨Gσ, Gτ, rfl, hσ, hτ⟩ := List.map_eq_append_iff.1 hG
  refine ⟨Gσ ++ (x, 0) :: Gτ, V, by simp [hσ, hτ], hV, ?_⟩
  rw [isAMGameVerifier_iff_value] at hA ⊢
  intro a
  simpa only [evalShape_append, evalShape_cons, Polynomial.eval_zero, value_insert_zero] using hA a

theorem AMGameClass_merge {enc : α ↪ List Bool} (σ τ : List AMMove) (x : AMMove) :
    AMGameClass enc (σ ++ x :: x :: τ) ⊆ AMGameClass enc (σ ++ x :: τ) := by
  rintro A ⟨G, V, hG, hV, hA⟩
  obtain ⟨Gσ, G', rfl, hσ, h'⟩ := List.map_eq_append_iff.1 hG
  obtain ⟨⟨x₁, p₁⟩, G'', rfl, rfl, h''⟩ := List.map_eq_cons_iff.1 h'
  obtain ⟨⟨x₂, p₂⟩, Gτ, rfl, rfl, hτ⟩ := List.map_eq_cons_iff.1 h''
  refine ⟨Gσ ++ (x₂, p₁ + p₂) :: Gτ, V, by simp [hσ, hτ], hV, ?_⟩
  rw [isAMGameVerifier_iff_value] at hA ⊢
  intro a
  cases x₂
  · simpa only [evalShape_append, evalShape_cons, Polynomial.eval_add, value_merge_arthur] using
      hA a
  · simpa only [evalShape_append, evalShape_cons, Polynomial.eval_add, value_merge_merlin] using
      hA a

/-- Game classes grow along sublists of move patterns, inside any fixed prefix. -/
theorem AMGameClass_mono_sublist_append {enc : α ↪ List Bool} {l₁ l₂ : List AMMove}
    (h : List.Sublist l₁ l₂) (σ : List AMMove) :
    AMGameClass enc (σ ++ l₁) ⊆ AMGameClass enc (σ ++ l₂) := by
  induction h generalizing σ with
  | slnil => exact le_rfl
  | cons x _ ih => exact (ih σ).trans (AMGameClass_insert σ _ x)
  | cons_cons x _ ih =>
    simpa only [List.append_assoc, List.singleton_append] using ih (σ ++ [x])

/-- **Padding**: game classes are monotone in the move pattern under `List.Sublist`. -/
theorem AMGameClass_mono {enc : α ↪ List Bool} {π₁ π₂ : List AMMove} (h : List.Sublist π₁ π₂) :
    AMGameClass enc π₁ ⊆ AMGameClass enc π₂ :=
  AMGameClass_mono_sublist_append h []

private theorem sum_toNat_eq_card {ι : Type} [Fintype ι] (f : ι → Bool) :
    ∑ i, (f i).toNat = #{i | f i = true} := by
  rw [card_filter]
  exact sum_congr rfl fun i _ => by cases f i <;> rfl

private theorem sup_toNat_eq {ι : Type} [Fintype ι] (f : ι → Bool) :
    (univ.sup fun i => (f i).toNat) = (decide (∃ i, f i = true)).toNat := by
  by_cases h : ∃ i, f i = true
  · obtain ⟨i, hi⟩ := h
    rw [decide_eq_true ⟨i, hi⟩]
    exact le_antisymm (Finset.sup_le fun j _ => Bool.toNat_le (f j))
      (by simpa [hi] using Finset.le_sup (f := fun i => (f i).toNat) (mem_univ i))
  · simp only [not_exists, Bool.not_eq_true] at h
    simp [h]

/-- The one-move shape `[(x, p)]` of a polynomial game. -/
private theorem map_fst_eq_singleton {G : List (AMMove × Polynomial ℕ)} {x : AMMove}
    (h : G.map Prod.fst = [x]) : ∃ p : Polynomial ℕ, G = [(x, p)] := by
  match G, h with
  | [(_, p)], rfl => exact ⟨p, rfl⟩

/-- The two-move shape `[(x, p), (y, q)]` of a polynomial game. -/
private theorem map_fst_eq_pair {G : List (AMMove × Polynomial ℕ)} {x y : AMMove}
    (h : G.map Prod.fst = [x, y]) : ∃ p q : Polynomial ℕ, G = [(x, p), (y, q)] := by
  match G, h with
  | [(_, p), (_, q)], rfl => exact ⟨p, q, rfl⟩

/-- A zero-move game verifier is a deterministic decider on the empty transcript. -/
theorem isAMGameVerifier_nil_iff {enc : α ↪ List Bool} {V : α × List Bool → Bool} {A : Set α} :
    IsAMGameVerifier enc [] V A ↔ ∀ a, a ∈ A ↔ V (a, []) = true := by
  refine forall_congr' fun a => ?_
  simp only [evalShape, List.map_nil, arthurBits, pow_zero, mul_one, count_nil]
  by_cases ha : a ∈ A <;> cases V (a, []) <;> simp [ha]

/-- A single-move Arthur game verifier is a bounded-error decider. -/
theorem isAMGameVerifier_arthur_iff {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} :
    IsAMGameVerifier enc [(.arthur, p)] V A ↔ DecidesWithBoundedError enc p V A := by
  refine forall_congr' fun a => ?_
  simp only [evalShape, List.map_cons, List.map_nil, count_arthur, count_nil, List.append_nil,
    sum_toNat_eq_card, arthurBits, add_zero]
  exact and_congr (imp_congr_right fun _ => boundedErrorAt_true_iff.symm)
    (imp_congr_right fun _ => boundedErrorAt_false_iff.symm)

/-- A single-move Merlin game verifier is an `NP` verifier. -/
theorem isAMGameVerifier_merlin_iff {enc : α ↪ List Bool} {q : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} :
    IsAMGameVerifier enc [(.merlin, q)] V A ↔ IsVerifier enc q V A := by
  refine forall_congr' fun a => ?_
  simp only [evalShape, List.map_cons, List.map_nil, count_merlin, count_nil, List.append_nil,
    sup_toNat_eq, arthurBits, pow_zero, mul_one]
  have hex : (∃ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn y) = true) ↔
      ∃ w : List Bool, w.length = q.eval (enc a).length ∧ V (a, w) = true :=
    ⟨fun ⟨y, hy⟩ => ⟨List.ofFn y, List.length_ofFn, hy⟩,
      fun ⟨w, hw, hVw⟩ => ⟨BitString.ofList _ w, by rwa [BitString.ofFn_ofList hw]⟩⟩
  by_cases ha : a ∈ A <;>
    by_cases hy : ∃ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn y) = true <;>
    simp [ha, hy, ← hex]

theorem isAMGameVerifier_arthur_merlin_iff {enc : α ↪ List Bool} {p q : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} :
    IsAMGameVerifier enc [(.arthur, p), (.merlin, q)] V A ↔ IsArthurMerlinVerifier enc p q V A := by
  refine forall_congr' fun a => ?_
  have hc : count (evalShape [(.arthur, p), (.merlin, q)] (enc a).length)
      (fun t => V (a, t)) = #{r : Fin (p.eval (enc a).length) → Bool |
        ∃ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true} := by
    simp only [evalShape, List.map_cons, List.map_nil, count_arthur, count_merlin,
      count_nil, List.append_nil, sup_toNat_eq, sum_toNat_eq_card, decide_eq_true_eq]
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset
    (Fin (p.eval (enc a).length) → Bool))) fun r =>
      ∃ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true
  simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, not_exists,
    Bool.not_eq_true] at hsum
  rw [hc]
  simp only [evalShape, List.map_cons, List.map_nil, arthurBits, add_zero]
  exact and_congr_right fun _ => imp_congr_right fun _ => by omega

theorem isAMGameVerifier_merlin_arthur_iff {enc : α ↪ List Bool} {q p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} :
    IsAMGameVerifier enc [(.merlin, q), (.arthur, p)] V A ↔ IsMerlinArthurVerifier enc q p V A := by
  refine forall_congr' fun a => ?_
  set f : (Fin (q.eval (enc a).length) → Bool) → ℕ := fun y =>
    #{r : Fin (p.eval (enc a).length) → Bool | V (a, List.ofFn y ++ List.ofFn r) = true}
  have hsum (y : Fin (q.eval (enc a).length) → Bool) :
      f y + #{r : Fin (p.eval (enc a).length) → Bool | V (a, List.ofFn y ++ List.ofFn r) = false} =
        2 ^ p.eval (enc a).length := by
    simpa only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Bool.not_eq_true] using card_filter_add_card_filter_not
      (s := (univ : Finset (Fin (p.eval (enc a).length) → Bool))) fun r =>
        V (a, List.ofFn y ++ List.ofFn r) = true
  simp only [evalShape, List.map_cons, List.map_nil, count_arthur, count_merlin, count_nil,
    List.append_nil, sum_toNat_eq_card, arthurBits, add_zero, BoundedErrorAt]
  refine and_congr (imp_congr_right fun _ => ⟨fun h => ?_, fun ⟨y, hy⟩ => ?_⟩)
    (imp_congr_right fun _ => ⟨fun h y => ?_, fun h => ?_⟩)
  · obtain ⟨y, -, hy⟩ := exists_mem_eq_sup univ univ_nonempty f
    exact ⟨y, by rwa [hy] at h⟩
  · exact hy.trans (Nat.mul_le_mul_left 3 (Finset.le_sup (f := f) (mem_univ y)))
  · linarith [hsum y, (Nat.mul_le_mul_left 3 (Finset.le_sup (f := f) (mem_univ y))).trans h]
  · obtain ⟨y, -, hy⟩ := exists_mem_eq_sup univ univ_nonempty f
    linarith [hy, h y, hsum y]

/-- **The empty game `[]` is `P`.** -/
theorem AMGameClass_nil {enc : α ↪ List Bool} : AMGameClass enc [] = P enc := by
  ext A
  refine ⟨fun ⟨G, V, hG, hV, hA⟩ => ?_, fun ⟨f, hf, hA⟩ =>
    ⟨[], fun x => f x.1, rfl, hf.comp (.fst enc encBits), isAMGameVerifier_nil_iff.2 hA⟩⟩
  rw [List.map_eq_nil_iff.1 hG] at hA
  exact ⟨fun a => V (a, []), by fun_prop, isAMGameVerifier_nil_iff.1 hA⟩

/-- **The game `A` is `BPP`.** -/
theorem AMGameClass_arthur {enc : α ↪ List Bool} : AMGameClass enc [.arthur] = BPP enc := by
  ext A
  refine ⟨fun ⟨G, V, hG, hV, hA⟩ => ?_, fun ⟨p, V, hV, hA⟩ =>
    ⟨[(.arthur, p)], V, rfl, hV, isAMGameVerifier_arthur_iff.2 hA⟩⟩
  obtain ⟨p, rfl⟩ := map_fst_eq_singleton hG
  exact ⟨p, V, hV, isAMGameVerifier_arthur_iff.1 hA⟩

/-- **The game `M` is `NP`.** -/
theorem AMGameClass_merlin {enc : α ↪ List Bool} : AMGameClass enc [.merlin] = NP enc := by
  ext A
  refine ⟨fun ⟨G, V, hG, hV, hA⟩ => ?_, fun ⟨q, V, hV, hA⟩ =>
    ⟨[(.merlin, q)], V, rfl, hV, isAMGameVerifier_merlin_iff.2 hA⟩⟩
  obtain ⟨q, rfl⟩ := map_fst_eq_singleton hG
  exact ⟨q, V, hV, isAMGameVerifier_merlin_iff.1 hA⟩

/-- **The game `A M` is `AM`.** -/
theorem AMGameClass_arthur_merlin {enc : α ↪ List Bool} :
    AMGameClass enc [.arthur, .merlin] = AM enc := by
  ext A
  refine ⟨fun ⟨G, V, hG, hV, hA⟩ => ?_, fun ⟨p, q, V, hV, hA⟩ =>
    ⟨[(.arthur, p), (.merlin, q)], V, rfl, hV, isAMGameVerifier_arthur_merlin_iff.2 hA⟩⟩
  obtain ⟨p, q, rfl⟩ := map_fst_eq_pair hG
  exact ⟨p, q, V, hV, isAMGameVerifier_arthur_merlin_iff.1 hA⟩

/-- **The game `M A` is `MA`.** -/
theorem AMGameClass_merlin_arthur {enc : α ↪ List Bool} :
    AMGameClass enc [.merlin, .arthur] = MA enc := by
  ext A
  refine ⟨fun ⟨G, V, hG, hV, hA⟩ => ?_, fun ⟨q, p, V, hV, hA⟩ =>
    ⟨[(.merlin, q), (.arthur, p)], V, rfl, hV, isAMGameVerifier_merlin_arthur_iff.2 hA⟩⟩
  obtain ⟨q, p, rfl⟩ := map_fst_eq_pair hG
  exact ⟨q, p, V, hV, isAMGameVerifier_merlin_arthur_iff.1 hA⟩

theorem AMk_zero {enc : α ↪ List Bool} : AMk enc 0 = P enc := AMGameClass_nil

theorem MAk_zero {enc : α ↪ List Bool} : MAk enc 0 = P enc := AMGameClass_nil

theorem AMk_one {enc : α ↪ List Bool} : AMk enc 1 = BPP enc := AMGameClass_arthur

theorem MAk_one {enc : α ↪ List Bool} : MAk enc 1 = NP enc := AMGameClass_merlin

theorem AMk_two {enc : α ↪ List Bool} : AMk enc 2 = AM enc := AMGameClass_arthur_merlin

theorem MAk_two {enc : α ↪ List Bool} : MAk enc 2 = MA enc := AMGameClass_merlin_arthur

/-- Prepending a polynomially bounded existential quantifier over words prepends a Merlin move
to a public-coin game. -/
theorem mem_AMGameClass_cons_merlin {enc : α ↪ List Bool} {B : Set (α × List Bool)}
    {π : List AMMove} (hB : B ∈ AMGameClass (encPair enc encBits) π) (p : Polynomial ℕ) :
    {a | ∃ w : List Bool, w.length = p.eval (enc a).length ∧ (a, w) ∈ B} ∈
      AMGameClass enc (.merlin :: π) := by
  obtain ⟨G, VB, hG, hVB, hB'⟩ := hB
  set L : Polynomial ℕ := 2 * Polynomial.X + 1 + p with hLdef
  have hL (a : α) (y : Fin (p.eval (enc a).length) → Bool) :
      (encPair enc encBits (a, List.ofFn y)).length = L.eval (enc a).length := by
    simp only [length_encPair, encBits_apply, List.length_ofFn, hLdef, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  have hp : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
      (encPair enc encBits) encUnary :=
    ((ComputableInPolyTime.unary_eval p).comp (.encoding_length enc)).comp (.fst _ _)
  refine ⟨(.merlin, p) :: G.map (fun x => (x.1, x.2.comp L)),
    fun x => VB ((x.1, x.2.take (p.eval (enc x.1).length)),
      x.2.drop (p.eval (enc x.1).length)), ?_, ?_, fun a => ?_⟩
  · simp [Function.comp_def, hG]
  · exact hVB.comp (((ComputableInPolyTime.fst _ _).prod
      (.bitsTakeWithInput (.snd _ _) hp)).prod (.bitsDropWithInput (.snd _ _) hp))
  · have heval : evalShape (G.map fun x => (x.1, x.2.comp L)) (enc a).length =
        evalShape G (L.eval (enc a).length) := by
      simp [evalShape, List.map_map, Function.comp_def, Polynomial.eval_comp]
    simp only [evalShape_cons, heval, arthurBits, count_merlin, List.take_left' List.length_ofFn,
      List.drop_left' List.length_ofFn]
    set f : (Fin (p.eval (enc a).length) → Bool) → ℕ := fun y =>
      count (evalShape G (L.eval (enc a).length)) fun t => VB ((a, List.ofFn y), t)
    refine ⟨fun ⟨w, hw, hwB⟩ => ?_, fun ha => ?_⟩
    · let y := BitString.ofList (p.eval (enc a).length) w
      exact (hL a y ▸ (hB' (a, List.ofFn y)).1 (by rwa [BitString.ofFn_ofList hw])).trans
        (Nat.mul_le_mul_left 3 (Finset.le_sup (f := f) (mem_univ y)))
    · obtain ⟨y, -, hy⟩ := exists_mem_eq_sup univ univ_nonempty f
      rw [hy]
      simpa only [hL a y] using
        (hB' (a, List.ofFn y)).2 fun h => ha ⟨List.ofFn y, List.length_ofFn, h⟩

end Cslib.Complexity
