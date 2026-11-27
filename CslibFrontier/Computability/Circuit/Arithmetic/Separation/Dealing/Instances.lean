/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.ProgramTime
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.ScriptSize
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Time
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Theorem

/-!
# One cut by the dealing program, with numbers

The pieces of the dealing program of [AnthropicVPVNP2026] are the instances of a formula `GROUP`
at the scripts of the groups. If `GROUP` evaluates the groups of all plans at their scripts in
time linear in `groupTime` (`EvaluatesGroups`, which the program GROUP does:
`exists_evaluatesGroups`), then the dealing program cuts plain sums with explicit numbers
(`isCut_dealProgram_of_evaluatesGroups`): the pieces take `κ` times a bound `tB` of the time of
GROUP at the scripts, they have size at most `X + 1 + 200 * X ^ 3 * Lc` plus the letters of the
input parts of the group and the bits of its cut units, there are `mm` of them, and the dealing
program takes `dealTime` steps.

The codes of the dealing program have `Lc` bits if `2 ^ Lc` bounds the numbers of the names
(`Name.card_eq`), of the digits, of the row data and of the keys (`Codes.exists_lengthBounds`).

## Main definitions

* `Codes.LengthBounds`: codes of length at most `Lc`, with distinct keys.
* `EvaluatesGroups`: a formula that evaluates the groups of all plans at their scripts.

## Main results

* `Name.card_eq`: the number of the names of the values of the dealing program.
* `Codes.exists_lengthBounds`: codes of `Lc` bits.
* `exists_evaluatesGroups`: the program GROUP evaluates the groups.
* `isCut_dealProgram_of_evaluatesGroups`: the dealing program cuts, with numbers.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the proof of Theorem J.3
(pp. 53–54: the evaluator, and the program `G`, whose script has `(s/k + M/k)Λ` input symbols,
`τΛ/v^300` bits of cut packets and `v^O(1)` names and instructions). Ported from the source module
`Nc.Dl.Inst` (`thm_onecut_program`, `GroupOK`, `CodesLe`, `exists_codes`) and the numbers of
names of `Nc.Dl.GrpCost` (`card_nm`).
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Finset Interpreter Cut GroupProgram

/-! ### Codes -/

section Codes

/-- The number of the names of the values of the dealing program. -/
theorem Name.card_eq (K E pS : ℕ) (S N U : Type) [Fintype S] [Fintype N] [Fintype U] :
    Fintype.card (Name K E pS S N U) = 1 + K + (K + 1) + 3 * (Fintype.card (Option S) * (K + K)) +
      3 * ((K + K) * (K + K)) + (K + K) + 3 * Fintype.card N + pS + E + (E + 1) +
        2 * Fintype.card U := by
  rw [Fintype.card_congr (proxy_equiv% (Name K E pS S N U)).symm]
  simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Fintype.card_sigma,
    sum_const, card_univ, Fintype.card_option, smul_eq_mul, Fintype.card_bool]
  ring

/-- A finite type with at most `2 ^ L` elements has an injective code of `L` bits. -/
private theorem exists_code (α : Type*) [Fintype α] {L : ℕ} (h : Fintype.card α ≤ 2 ^ L) :
    ∃ code : α → List Bool, Injective code ∧ ∀ a, (code a).length = L := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (β := Fin L → Bool) (by simpa using h)
  exact ⟨fun a => List.ofFn (f a), List.ofFn_injective.comp f.injective, by simp⟩

variable {F : Type} [CommSemiring F] {K A' E U0 U1 D pS : ℕ} {M : Moves F (K + K + A') E}
  {S : Type} [Fintype S]

/-- Codes of the dealing program of length at most `Lc`: of the names, the digits, the row data,
the keys of the cells and the keys of the second copies, where no two keys are equal. -/
structure Codes.LengthBounds (C : Codes S M U0 U1 D pS) (Lc : ℕ) : Prop where
  /-- The codes of the names. -/
  name : ∀ y, (C.name y).length ≤ Lc
  /-- The codes of the digits. -/
  digit : ∀ d, (C.digit d).length ≤ Lc
  /-- The codes of the row data. -/
  rowData : ∀ d, (C.rowData d).length ≤ Lc
  /-- The keys of the cells. -/
  key : ∀ c, (C.key c).length ≤ Lc
  /-- The keys of the second copies. -/
  dkey : ∀ c, (C.dkey c).length ≤ Lc
  /-- No two keys are equal. -/
  injective : Injective (Sum.elim C.key C.dkey)

/-- **Codes of `Lc` bits.** If `2 ^ Lc` bounds the numbers of the names, the digits, the row data
and the keys, the dealing program has codes of length at most `Lc` with distinct keys. -/
theorem Codes.exists_lengthBounds {Lc : ℕ}
    (hname : Fintype.card (PlanName S M U0 U1 pS) ≤ 2 ^ Lc) (hD : D ≤ 2 ^ Lc)
    (hrow : Fintype.card (RowData (K + K)) ≤ 2 ^ Lc)
    (hkey : Fintype.card (Cell M U0 U1 ⊕ Fin (K + K) × Fin U0) ≤ 2 ^ Lc) :
    ∃ C : Codes S M U0 U1 D pS, C.LengthBounds Lc := by
  obtain ⟨f₁, i₁, l₁⟩ := exists_code _ hname
  obtain ⟨f₂, i₂, l₂⟩ := exists_code (Fin D) (by simpa using hD)
  obtain ⟨f₃, i₃, l₃⟩ := exists_code _ hrow
  obtain ⟨f₄, i₄, l₄⟩ := exists_code _ hkey
  exact ⟨⟨f₁, i₁, f₂, i₂, f₃, i₃, f₄ ∘ .inl, f₄ ∘ .inr⟩, fun _ => (l₁ _).le, fun _ => (l₂ _).le,
    fun _ => (l₃ _).le, fun _ => (l₄ _).le, fun _ => (l₄ _).le, by simpa using i₄⟩

end Codes

/-! ### The program GROUP -/

section Group

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S]
  [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}

/-- **What GROUP does.** The formula `GROUP`, with the constant `κ`, evaluates the groups of all
plans at their scripts, for the automaton `mu`, the code `cb` of its letters, the list `kinds` of
roles of laws and the numbers `qn` of the states: at the script of a group, with binary numbers
`bT` of steps and `bub` of bits of a unit and with distinct keys, its plain sum takes at most
`κ` times `groupTime` steps and is the value of the group, if units have bits, the plan is
`cap`-bounded, the input parts have at most `bT` letters, the row data of the rows that are not
empty are ordered, and `kinds` lists the roles. -/
def EvaluatesGroups (θ : List Bool → F) (mu : Tape.Letter S Unit Γ → Matrix Q Q F)
    (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : Cut.Law F, L.Role)) (qn : Q → ℕ)
    (GROUP : Fm) (κ : ℕ) : Prop :=
  ∀ {A' K E U0 U1 cap : ℕ} {G : Type} [DecidableEq G] {M : Moves F (K + K + A') E}
    (P : Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (o : M.Channel → Fin U1) (grp : Fin (K + K + A') → G) (g : G)
    (key : Cell M U0 U1 → List Bool) (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.Role → ℕ)
    (bT bub : List Bool)
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent (BitString.binaryValue bub)),
    Injective (Sum.elim key dkey) → 0 < BitString.binaryValue bub → P.Ok cap →
    (∀ κ, (x κ).length ≤ BitString.binaryValue bT) →
    (∀ s p, (ρ s p).empty = false → (ρ s p).first ≤ (ρ s p).last) →
    (∀ r, kinds[tg r]? = some ⟨M.law r.1, r.2⟩) →
    let l := groupScript qn cb P q x ρ n o grp g key dkey tg b
    Plain θ (κ * groupTime bT bub l) (.cons GROUP.code (scriptEnc bT bub l)) ∧
      pv θ (.cons GROUP.code (scriptEnc bT bub l)) =
        P.groupValue mu (BitString.binaryValue bT) cb q x ρ n o grp g b

/-- **The program GROUP evaluates the groups**, for an automaton `mu` and roles `kinds` whose
entries are values of formulas, with the numbers of the states in a fixed enumeration. -/
theorem exists_evaluatesGroups {θ : List Bool → F} (mu : Tape.Letter S Unit Γ → Matrix Q Q F)
    (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : Cut.Law F, L.Role))
    (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q')
    (htab : ∀ z ∈ kinds, ∀ i v g', ∃ e : WE, e.val θ = z.1.table z.2 i v g') :
    ∃ (GROUP : Fm) (κ : ℕ),
      EvaluatesGroups θ mu cb kinds (fun z => (Fintype.equivFin Q z : ℕ)) GROUP κ := by
  obtain ⟨GROUP, κ, h⟩ := exists_group mu cb kinds hmu htab
  exact ⟨GROUP, κ, fun P q x ρ n o grp g key dkey tg bT bub b h₁ h₂ h₃ h₄ h₅ h₆ =>
    (h P q x ρ n o grp g key dkey tg bT bub b h₁ h₂ h₃ h₄ h₅ h₆).imp_right And.left⟩

end Group

/-! ### One cut -/

section Cut

/-- At most `bd` units with exactly one holder in every group make at most `bd` cut units per
group. -/
private theorem card_cutUnits_le {U A G : Type*} [Fintype G] [DecidableEq G]
    {h : U → Bool → A} {grp : A → G} {cur : Finset U} {bd : ℕ}
    (hbd : ∀ g, #(cur.filter (OneIn h grp g)) ≤ bd) :
    #(Play.cutUnits h grp cur) ≤ Fintype.card G * bd := by
  classical
  refine (card_le_card (t := univ.biUnion fun g => cur.filter (OneIn h grp g)) fun u hu => ?_).trans
    (card_biUnion_le.trans ((sum_le_sum fun g _ => hbd g).trans (by simp)))
  obtain ⟨hu, hne⟩ := Play.mem_cutUnits.1 hu
  exact mem_biUnion.2 ⟨grp (h u false), mem_univ _, mem_filter.2 ⟨hu, Or.inl ⟨rfl, Ne.symm hne⟩⟩⟩

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S]
  [DecidableEq S] [Fintype Q] [DecidableEq Q] {K A' E U0 U1 D nI pS mm c : ℕ}
  {M : Moves F (K + K + A') E} {P : Plan M U0 U1}
  {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm} {C : Codes S M U0 U1 D pS}
  {θ : List Bool → F} {mu : Tape.Letter S Unit Γ → Matrix Q Q F} {cb : Option Γ → Fin c → Bool}
  {kinds : List (Σ L : Cut.Law F, L.Role)} {qn : Q → ℕ} {tg : M.Role → ℕ} {GROUP : Fm} {κ : ℕ}
  {bT bub nl nub : List Bool} {hD : 1 < D} {hmm : mm ≤ D} {bt : Bool → Γ} {i e : Q}
  {hU0 : U0 < D} {hU1 : U1 ≤ D} {X Lc T ub ℓ τ s cap bd ιb tB : ℕ}

/-- **One cut, with numbers.** Let `X` and `Lc` bound the numbers and the lengths of the codes of
the dealing program, with distinct keys, let `GROUP` evaluate the groups with the constant `κ`,
let the bits `bT`, `bub`, `nl`, `nub` of the number `T` of steps of a block, the number `ub` of
bits of a unit and the length `ℓ ≤ T` of a part have at most `Lc` digits, and let the universal
automaton and the formula of the pieces give the plain sums of arguments of size at most `s`, as
in `isCut_dealProgram`. If every choice that passes the checks has at most `bd` units with one
holder in each group, at most `ιb` base parties in each group, moves of at most `X` units each,
and a time of GROUP at most `tB` at every script with parts of at most `T` letters, and the code
of `GROUP` has size at most `X`, then the dealing program cuts `(τ, s)` into
`(κ * tB, X + 1 + (200 * X ^ 3 * Lc + ιb * ℓ * (4 * c + 2) + bd * (4 * ub)))` with at most `mm`
pieces in `dealTime Lc X K mm ub (mm * bd) s` steps. -/
theorem isCut_dealProgram_of_evaluatesGroups (tab : SlpTab P grp D nI pS)
    [DecidablePred tab.Valid] [∀ n o x, Decidable (P.Good n o x)] (hK : 0 < K)
    (H : C.SizeBounds qn tg X Lc) (hkey : Injective (Sum.elim C.key C.dkey))
    (hGR : EvaluatesGroups θ mu cb kinds qn GROUP κ)
    (hkind : ∀ r, kinds[tg r]? = some ⟨M.law r.1, r.2⟩) (hP : P.Ok cap)
    (hT : BitString.binaryValue bT = T) (hub : BitString.binaryValue bub = ub) (hub0 : 0 < ub)
    (hnl : KT.val nl = ℓ) (hnub : KT.val nub = ub) (hℓ : ℓ ≤ T) (hlbT : bT.length ≤ Lc)
    (hlbub : bub.length ≤ Lc) (hlnl : nl.length ≤ Lc) (hlnub : nub.length ≤ Lc)
    (hU : ∀ z : Tree, z.size ≤ s → Plain θ τ z →
      Tape.runVal mu i e (K * T) (fun _ => (tbits z).map bt) = pv θ z)
    (hval : ∀ z : Tree, z.size ≤ s → Tape.runVal mu i e (K * T) (fun _ => (tbits z).map bt) =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1), if tab.Valid n then
            ∑ o : M.Channel → Fin U1, if ∀ x, P.Good n o x then
              ∑ b ∈ Play.common (none : UnitContent ub)
                (Play.cutUnits (UnitId.holder M.channelParty) (grp ⟨n, o⟩) (P.cur n o E)),
                ∏ g, P.groupValue mu T cb q (parts ℓ ((tbits z).map bt)) ρ n o (grp ⟨n, o⟩) g b
            else 0 else 0 else 0 else 0)
    (hbd : ∀ n o, tab.Valid n → (∀ x, P.Good n o x) → ∀ g,
      #((P.cur n o E).filter (OneIn (UnitId.holder M.channelParty) (grp ⟨n, o⟩) g)) ≤ bd)
    (hbase : ∀ n o, tab.Valid n → (∀ x, P.Good n o x) → ∀ g,
      #{p : Fin (K + K) | grp ⟨n, o⟩ (Fin.castAdd A' p) = g} ≤ ιb)
    (hcount : ∀ n o, tab.Valid n → (∀ x, P.Good n o x) → ∀ y, P.count n o y ≤ X)
    (hgp : GROUP.code.size ≤ X)
    (htB : ∀ (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
      (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
      (o : M.Channel → Fin U1) (g : Fin mm) (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub),
      (∀ κ, (x κ).length ≤ T) → tab.Valid n → (∀ x, P.Good n o x) →
        groupTime bT bub (groupScript qn cb P q x ρ n o (grp ⟨n, o⟩) g C.key C.dkey tg b) ≤ tB) :
    IsCut θ τ s (κ * tB) (X + 1 + (200 * X ^ 3 * Lc + ιb * ℓ * (4 * c + 2) + bd * (4 * ub))) mm
      (dealTime Lc X K mm ub (mm * bd) s)
      (C.dealProgram tab qn tg bT bub nl nub hD hmm GROUP.code cb bt i e hU0 hU1).code := by
  subst hT hub
  refine isCut_dealProgram C tab hK hnl hnub hU hval (fun z hz => ?_) fun z hz q ρ n o b g hρ hn ho
    _ => ?_
  · simpa using dealProgram_does tab H hK hnl hnub hlnl hlnub
      (fun n o hn ho => card_cutUnits_le (hbd n o hn ho)) z hz
  simp only [Tree.size]
  set x := parts ℓ ((tbits z).map bt)
  have hx (κ : Fin K) : (x κ).length ≤ BitString.binaryValue bT :=
    (length_parts_le _ _ _).trans hℓ
  have hρ' (s p) (hs : (ρ s p).empty = false) : (ρ s p).first ≤ (ρ s p).last := by
    have := hρ s p
    simp only [ValidRow, hs, Bool.false_eq_true, ↓reduceIte] at this
    exact this.2
  obtain ⟨h₁, h₂⟩ := hGR P q x ρ n o (grp ⟨n, o⟩) g C.key C.dkey tg bT bub b hkey hub0 hP hx hρ'
    hkind
  refine ⟨?_, h₁.of_le (Nat.mul_le_mul_left κ (htB q x ρ n o g b hx hn ho)), h₂⟩
  have hs := size_scriptEnc_le (qn := qn) (cb := cb) (q := q) (x := x) (ρ := ρ) (grp := grp ⟨n, o⟩)
    (g := g) (key := C.key) (dkey := C.dkey) (tg := tg) H.one_le_X H.one_le_Lc H.parties
    (Nat.le_of_succ_le H.initUnits) H.newUnits H.tapes H.units H.roles H.slotsAt H.channelsAt H.key
    H.dkey H.stateNum (fun r => by have := H.roleNum r; omega) (hcount n o hn ho) hlbT hlbub b
  have hp : ∑ κ with grp ⟨n, o⟩ (Fin.castAdd A' (Fin.natAdd K κ)) = g, (x κ).length ≤ ιb * ℓ := by
    refine (sum_le_card_nsmul _ _ ℓ fun κ _ => length_parts_le _ _ _).trans ?_
    rw [smul_eq_mul]
    refine Nat.mul_le_mul_right ℓ ((card_le_card_of_injOn (Fin.natAdd K) (fun κ hκ => ?_)
      (Fin.natAdd_injective K K).injOn).trans (hbase n o hn ho g))
    simpa using hκ
  have := Nat.mul_le_mul_right (4 * c + 2) hp
  have := Nat.mul_le_mul_right (4 * BitString.binaryValue bub) (hbd n o hn ho g)
  omega

end Cut

end Cslib.Circuits.Arithmetic.Separation.Dealing
