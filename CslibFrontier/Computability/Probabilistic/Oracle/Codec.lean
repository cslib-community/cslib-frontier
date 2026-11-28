/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Probability.PMF.Map

/-!
# Computational oracle codecs and typed-to-word simulation

`Cslib.OracleCodec` (`CslibFrontier.Languages.Probabilistic.Oracle.Codec`) adapts word-oracle
programs `WordOracleComp Op α` to typed oracles via `OracleCodec.adapt` and
`OracleCodec.wordOracle`. This module supplies the dual typed-to-word direction and strict
`IsOraclePPTOn` composition rules, with explicit reply caps, reply decoders, and fallback queries
(no hidden encoding typeclasses):

1. **Fixed-width bit-string codecs (`OracleCodec.bitStrings`)**: `n`-bit queries with `w`-bit
   replies on the single word channel, specializing at `w = n` to `OracleCodec.bitString n`.
2. **Typed-to-word lifting (`OracleCodec.queryWord`, `OracleCodec.toWord`)**: translates a typed
   program `ProbOracleComp (fun _ : Q => R) α` into `WordOracleComp Op α` by charging a prefix
   `List.take (replyCap q)` of each word reply and applying `decodeReply q`. Under `c.wordOracle`,
   `runWith_wordOracle_toWord` and `run_wordOracle_toWord` establish exact joint-state and output
   bisimulation whenever supported replies fit in `replyCap q`; `adapt_toWord` gives the syntactic
   round-trip when the cap holds for all replies; and `isCostBounded_toWord` /
   `isQueryBounded_toWord` preserve query budgets.
3. **Strict `IsOraclePPTOn` composition (`IsOraclePPTOn.queryWord`,
   `IsOraclePPTOn.wordOracle_state`, `IsOraclePPTOn.run_wordOracle_open`)**: certifies
   typed-to-word calls across multi-channel `Op` via `IsOraclePPTOn.finite_cases`, lifts typed
   stateful handlers to word handlers via `c.wordOracle`, and substitutes them into strict
   oracle-PPT word programs via `IsOraclePPTOn.run_interpret_preprocess_open` while restricting
   invariant obligations to valid typed queries.

## Main definitions

* `Cslib.OracleCodec.bitStrings`: `n`-bit queries with `w`-bit replies on channel `Unit`.
* `Cslib.OracleCodec.queryWord`, `Cslib.OracleCodec.toWord`: explicit capped typed-to-word query and
  program translation.

## Main results

* `Cslib.OracleCodec.adapt_toWord`, `Cslib.OracleCodec.runWith_wordOracle_toWord`,
  `Cslib.OracleCodec.run_wordOracle_toWord`: syntactic round-trip and stateful/stateless
  bisimulation against `c.wordOracle`.
* `Cslib.OracleCodec.isCostBounded_toWord`, `Cslib.OracleCodec.isQueryBounded_toWord`: query-budget
  preservation for `toWord`.
* `Cslib.Probability.IsOraclePPTOn.queryWord`,
  `Cslib.Probability.IsOraclePPTOn.wordOracle_state`,
  `Cslib.Probability.IsOraclePPTOn.run_wordOracle_open`: strict `IsOraclePPTOn` certificates for
  typed-to-word calls and open stateful `wordOracle` substitution.
-/

public section

namespace Cslib.OracleCodec

open Probability

/-- `n`-bit queries with `w`-bit replies on the single word channel `Unit`: a request carries a
query if and only if its payload has `n` bits. -/
@[expose] def bitStrings (n w : ℕ) : OracleCodec Unit (BitString n) fun _ => BitString w where
  encodeQuery x := ((), List.ofFn x)
  decodeQuery request := if request.2.length = n then some (BitString.ofList n request.2) else none
  decodeQuery_eq_some_iff := by
    rintro ⟨⟨⟩, word⟩ x
    by_cases hlength : word.length = n
    · simp only [hlength, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and]
      exact ⟨fun h => h ▸ BitString.ofFn_ofList hlength, fun h => h ▸ BitString.ofList_ofFn x⟩
    · simp only [hlength, ↓reduceIte, reduceCtorEq, false_iff, Prod.mk.injEq, true_and]
      rintro rfl
      simp at hlength
  encodeReply _ := ⟨List.ofFn, List.ofFn_injective⟩

/-- At equal input and output widths, `bitStrings n n` is `bitString n`. -/
@[simp] theorem bitStrings_same (n : ℕ) : bitStrings n n = bitString n := rfl

section ToWord

variable {Op Q R α β : Type} (c : OracleCodec Op Q fun _ => R)

/-- Perform one typed query `q : Q` on the word channel `Op`: send `c.encodeQuery q`, read at most
`replyCap q` bits of the word reply, and decode them with `decodeReply q`. -/
@[expose] def queryWord (replyCap : Q → ℕ) (decodeReply : Q → List Bool → R) (q : Q) :
    WordOracleComp Op R :=
  decodeReply q <$> (List.take (replyCap q) <$> ProbOracleComp.query (c.encodeQuery q))

/-- Translate a typed oracle program `ProbOracleComp (fun _ : Q => R) α` into a
`WordOracleComp Op α` program using `c.queryWord replyCap decodeReply`, forwarding private coin
draws unchanged. -/
@[expose] def toWord (replyCap : Q → ℕ) (decodeReply : Q → List Bool → R)
    (program : ProbOracleComp (fun _ : Q => R) α) :
    WordOracleComp Op α :=
  ProbOracleComp.simulate (c.queryWord replyCap decodeReply) program

@[simp] theorem toWord_pure (replyCap : Q → ℕ) (decodeReply : Q → List Bool → R) (a : α) :
    c.toWord replyCap decodeReply (pure a) = pure a := rfl

@[simp] theorem toWord_bind (replyCap : Q → ℕ) (decodeReply : Q → List Bool → R)
    (program : ProbOracleComp (fun _ : Q => R) α)
    (next : α → ProbOracleComp (fun _ : Q => R) β) :
    c.toWord replyCap decodeReply (program >>= next) =
      c.toWord replyCap decodeReply program >>= fun a => c.toWord replyCap decodeReply (next a) :=
  ProbOracleComp.simulate_bind _ _ _

@[simp] theorem toWord_map (replyCap : Q → ℕ) (decodeReply : Q → List Bool → R) (f : α → β)
    (program : ProbOracleComp (fun _ : Q => R) α) :
    c.toWord replyCap decodeReply (f <$> program) =
      f <$> c.toWord replyCap decodeReply program :=
  ProbOracleComp.simulate_map _ _ _

@[simp] theorem toWord_sample (replyCap : Q → ℕ) (decodeReply : Q → List Bool → R)
    (program : ProbComp α) :
    c.toWord replyCap decodeReply (ProbOracleComp.sample program) =
      ProbOracleComp.sample program :=
  ProbOracleComp.simulate_sample _ _

@[simp] theorem toWord_query (replyCap : Q → ℕ) (decodeReply : Q → List Bool → R) (q : Q) :
    c.toWord replyCap decodeReply (ProbOracleComp.query q) =
      c.queryWord replyCap decodeReply q :=
  ProbOracleComp.simulate_query _ _

/-- **Syntactic round-trip (`adapt ∘ toWord = id`)**: when every encoded reply fits within
`replyCap q` and `decodeReply q` left-inverts `c.encodeReply q`, adapting `c.toWord` back to the
typed interface recovers `program` identically. -/
theorem adapt_toWord {replyCap : Q → ℕ} {decodeReply : Q → List Bool → R}
    (hcap : ∀ q r, (c.encodeReply q r).length ≤ replyCap q)
    (hdec : ∀ q r, decodeReply q (c.encodeReply q r) = r)
    (program : ProbOracleComp (fun _ : Q => R) α) :
    c.adapt (c.toWord replyCap decodeReply program) = program := by
  rw [adapt, toWord, ProbOracleComp.simulate_simulate]
  have hid : (fun q => ProbOracleComp.simulate (c.wordOracle ProbOracleComp.query)
      (c.queryWord replyCap decodeReply q)) = ProbOracleComp.query := by
    funext q
    simp only [queryWord, ProbOracleComp.simulate_map, ProbOracleComp.simulate_query,
      wordOracle_encodeQuery, Functor.map_map, List.take_of_length_le (hcap q _), hdec]
    exact id_map _
  have hsub : OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
      (ProbOracleComp.query (spec := fun _ : Q => R)) = OracleComp.query := funext fun
    | .inl n => ProbOracleComp.sample_unifFin n
    | .inr _ => rfl
  rw [hid, ProbOracleComp.simulate, hsub, OracleComp.substitute_query_eq_self]

/-- **Stateful `runWith` bisimulation**: running `c.toWord replyCap decodeReply program` against
`c.wordOracle oracle` has the exact same joint `(α × State)` distribution as running `program`
directly against `oracle`, provided every supported reply of `oracle` has encoded length at most
`replyCap q` and `decodeReply q` left-inverts `c.encodeReply q`. -/
theorem runWith_wordOracle_toWord {State : Type}
    (oracle : Q → StateT State PMF R)
    {replyCap : Q → ℕ} {decodeReply : Q → List Bool → R}
    (hcap : ∀ q s r s', (r, s') ∈ (oracle q s).support → (c.encodeReply q r).length ≤ replyCap q)
    (hdec : ∀ q r, decodeReply q (c.encodeReply q r) = r)
    (program : ProbOracleComp (fun _ : Q => R) α) (s : State) :
    ProbOracleComp.runWith (c.wordOracle oracle) (c.toWord replyCap decodeReply program) s =
      ProbOracleComp.runWith oracle program s := by
  rw [toWord, ProbOracleComp.runWith_simulate]
  have hstep : (fun q => ProbOracleComp.runWith (c.wordOracle oracle)
      (c.queryWord replyCap decodeReply q)) = oracle := by
    funext q st
    simp only [queryWord, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      wordOracle_encodeQuery]
    rw [show (c.encodeReply q <$> oracle q) st = ((c.encodeReply q <$> oracle q)).run st from rfl,
      StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp, PMF.map_comp]
    refine (PMF.map_congr_on_support (oracle q st) _ _root_.id fun ⟨r, s'⟩ hmem => ?_).trans
      (PMF.map_id _)
    simp only [Function.comp_def, Prod.map_apply, id_eq]
    rw [List.take_of_length_le (hcap q st r s' hmem), hdec q r]
  rw [hstep]

/-- **Stateless `ProbComp` bisimulation**: evaluating `(c.toWord replyCap decodeReply program).run
(c.wordOracle oracle)` matches `program.run oracle` whenever every supported reply of `oracle` fits
in `replyCap q`. -/
theorem run_wordOracle_toWord (oracle : Q → ProbComp R)
    {replyCap : Q → ℕ} {decodeReply : Q → List Bool → R}
    (hcap : ∀ q r, r ∈ (ProbComp.eval (oracle q)).support → (c.encodeReply q r).length ≤ replyCap q)
    (hdec : ∀ q r, decodeReply q (c.encodeReply q r) = r)
    (program : ProbOracleComp (fun _ : Q => R) α) :
    ProbComp.eval ((c.toWord replyCap decodeReply program).run (c.wordOracle oracle)) =
      ProbComp.eval (program.run oracle) := by
  let stOracle (q : Q) : StateT Unit PMF R := fun s => (ProbComp.eval (oracle q)).map (·, s)
  have hstate : c.wordOracle stOracle =
      fun req (s : Unit) => (ProbComp.eval (c.wordOracle oracle req)).map (·, s) := by
    funext req ⟨⟩
    unfold wordOracle
    cases c.decodeQuery req with
    | none =>
      change ((pure [] : StateT Unit PMF (List Bool))).run () = _
      simp [StateT.run_pure, PMF.monad_pure_eq_pure, ProbComp.eval_pure]
    | some q =>
      dsimp only
      change ((c.encodeReply q <$> stOracle q)).run () = _
      rw [StateT.run_map]
      simp [stOracle, StateT.run, PMF.monad_map_eq_map, ProbComp.eval_map, PMF.map_comp,
        Function.comp_def]
  have hrun := c.runWith_wordOracle_toWord stOracle
    (replyCap := replyCap) (decodeReply := decodeReply)
    (fun q _ r _ hmem => by
      obtain ⟨r', hr', heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
      exact (Prod.mk.inj heq).1 ▸ hcap q r' hr')
    hdec program ()
  rw [hstate, ProbOracleComp.runWith_memoryless, ProbOracleComp.runWith_memoryless] at hrun
  have hid : (Prod.fst ∘ fun x : α => (x, ())) = _root_.id := rfl
  simpa only [PMF.map_comp, hid, PMF.map_id, ProbOracleComp.eval_run,
    OracleComp.evalWith_eq_interpret] using congrArg (PMF.map Prod.fst) hrun

/-- `toWord` preserves cost budgets whenever each encoded word request costs at most the typed
query's cost. -/
theorem isCostBounded_toWord {cost : Q → ℕ} {wordCost : Op × List Bool → ℕ}
    (replyCap : Q → ℕ) (decodeReply : Q → List Bool → R)
    (hcost : ∀ q, wordCost (c.encodeQuery q) ≤ cost q)
    {program : ProbOracleComp (fun _ : Q => R) α} {n : ℕ}
    (h : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) cost) program n) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) wordCost)
      (c.toWord replyCap decodeReply program) n := by
  refine ProbOracleComp.isCostBounded_simulate (fun q => ?_) h
  simp only [queryWord, OracleComp.isCostBounded_map_iff]
  exact (ProbOracleComp.isCostBounded_query wordCost (c.encodeQuery q)).mono (hcost q)

/-- `toWord` preserves external query budgets (`IsQueryBounded`). -/
theorem isQueryBounded_toWord (replyCap : Q → ℕ) (decodeReply : Q → List Bool → R)
    {program : ProbOracleComp (fun _ : Q => R) α} {n : ℕ}
    (h : program.IsQueryBounded n) :
    (c.toWord replyCap decodeReply program).IsQueryBounded n :=
  c.isCostBounded_toWord replyCap decodeReply (fun _ => le_rfl) h

end ToWord

end Cslib.OracleCodec

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- Performing a single typed query `c.queryWord` over a finite multi-channel word interface `Op` is
strict oracle PPT whenever `c.encodeQuery`, `replyCap`, and `decodeReply` are computable in plain
polynomial time. -/
@[fun_prop]
theorem IsOraclePPTOn.queryWord {Op Q R α : Type} [DecidableEq Op] [Finite Op]
    (c : OracleCodec Op Q fun _ => R)
    {input : α ↪ List Bool} {opEncoding : Op ↪ List Bool} {replyEncoding : R ↪ List Bool}
    {replyCap : α → Q → ℕ} {decodeReply : Q → List Bool → R} {q : α → Q}
    (henc : ComputableInPolyTime (fun a => c.encodeQuery (q a))
      input (encPair opEncoding encBits))
    (hcap : ComputableInPolyTime (fun a => replyCap a (q a)) input encUnary)
    (hdec : ComputableInPolyTime (fun p : α × List Bool => decodeReply (q p.1) p.2)
      (encPair input encBits) replyEncoding) :
    IsOraclePPTOn input replyEncoding
      (fun a => c.queryWord (replyCap a) decodeReply (q a)) := by
  exact (IsOraclePPTOn.query_take_with henc.fst' henc.snd' hcap).map_with
    (f := fun a w => decodeReply (q a) w) hdec

/-- Lifting a strict oracle-PPT typed stateful handler `typed : Caller → Q → StateT State
(WordOracleComp External) R` through `c.wordOracle` produces a strict oracle-PPT word handler on
`encHandlerCall`. The explicit `defaultQuery : Q` is used only as the dead fallback of `Option.getD`
after testing `(c.decodeQuery request).isSome`. -/
theorem IsOraclePPTOn.wordOracle_state
    {Op External Q R Caller State : Type} [DecidableEq External]
    (c : OracleCodec Op Q fun _ => R) (defaultQuery : Q)
    {input : Caller ↪ List Bool} {opEncoding : Op ↪ List Bool}
    {queryEncoding : Q ↪ List Bool} {replyEncoding : R ↪ List Bool}
    {stateEncoding : State ↪ List Bool}
    {typed : Caller → Q → StateT State (WordOracleComp External) R}
    (hdecode : ComputableInPolyTime c.decodeQuery
      (encPair opEncoding encBits) (encOption queryEncoding))
    (hencodeReply : ComputableInPolyTime (fun p : Q × R => c.encodeReply p.1 p.2)
      (encPair queryEncoding replyEncoding) encBits)
    (htyped : IsOraclePPTOn
      (encPair input (encPair queryEncoding stateEncoding))
      (encPair replyEncoding stateEncoding)
      (fun p => typed p.1 p.2.1 p.2.2)) :
    IsOraclePPTOn (encHandlerCall input opEncoding stateEncoding)
      (encPair encBits stateEncoding)
      (fun ⟨caller, request, state⟩ => c.wordOracle (typed caller) request state) := by
  have : Finite External := htyped.finite_operations
  let EIn := encHandlerCall input opEncoding stateEncoding
  let EOut := encPair encBits stateEncoding
  have hcaller : ComputableInPolyTime
      (fun x : Caller × (Op × List Bool) × State => x.1) EIn input := by
    dsimp only [EIn, encHandlerCall]; fun_prop
  have hreq : ComputableInPolyTime
      (fun x : Caller × (Op × List Bool) × State => x.2.1) EIn (encPair opEncoding encBits) := by
    dsimp only [EIn, encHandlerCall]; fun_prop
  have hstate : ComputableInPolyTime
      (fun x : Caller × (Op × List Bool) × State => x.2.2) EIn stateEncoding := by
    dsimp only [EIn, encHandlerCall]; fun_prop
  have hopt : ComputableInPolyTime
      (fun x : Caller × (Op × List Bool) × State => c.decodeQuery x.2.1)
      EIn (encOption queryEncoding) := hdecode.comp hreq
  have hgetQ : ComputableInPolyTime
      (fun x : Caller × (Op × List Bool) × State => (c.decodeQuery x.2.1).getD defaultQuery)
      EIn queryEncoding := by fun_prop
  have hcall : IsOraclePPTOn EIn (encPair replyEncoding stateEncoding)
      (fun x : Caller × (Op × List Bool) × State =>
        typed x.1 ((c.decodeQuery x.2.1).getD defaultQuery) x.2.2) :=
    htyped.preprocess (hcaller.prod (hgetQ.prod hstate))
  have hpost : ComputableInPolyTime
      (fun p : (Caller × (Op × List Bool) × State) × (R × State) =>
        (c.encodeReply ((c.decodeQuery p.1.2.1).getD defaultQuery) p.2.1, p.2.2))
      (encPair EIn (encPair replyEncoding stateEncoding)) EOut := by
    fun_prop
  refine (IsOraclePPTOn.cond
    (condition := fun x : Caller × (Op × List Bool) × State => (c.decodeQuery x.2.1).isSome)
    (by fun_prop)
    (hcall.map_with
      (f := fun x res => (c.encodeReply ((c.decodeQuery x.2.1).getD defaultQuery) res.1, res.2))
      hpost)
    (ComputableInPolyTime.isOraclePPTOn
      (f := fun ⟨_caller, _req, state⟩ => (([] : List Bool), state))
      (by fun_prop))).congr ?_
  rintro ⟨caller, request, state⟩ ExtState oracle ext
  refine congrArg (fun p => ProbOracleComp.runWith oracle p ext) ?_
  dsimp only [OracleCodec.wordOracle]
  cases c.decodeQuery request with
  | none => rfl
  | some q =>
    simp only [Option.isSome_some, ↓reduceIte, Option.getD_some]
    rw [show (c.encodeReply q <$> typed caller q) state =
        ((c.encodeReply q <$> typed caller q)).run state from rfl,
      StateT.run_map]
    rfl

/-- Open stateful substitution through `c.wordOracle`: certify running an `IsOraclePPTOn` word
program against `c.wordOracle (typed a)` from `initial a`, checking invariant preservation and
reply/state size bounds only on valid typed queries `q : Q` (with `request = c.encodeQuery q`). -/
theorem IsOraclePPTOn.run_wordOracle_open
    {Op External Q R α β Caller State : Type} [DecidableEq Op] [DecidableEq External]
    (c : OracleCodec Op Q fun _ => R) (defaultQuery : Q)
    {source : α ↪ List Bool} {input : Caller ↪ List Bool} {output : β ↪ List Bool}
    {opEncoding : Op ↪ List Bool} {queryEncoding : Q ↪ List Bool} {replyEncoding : R ↪ List Bool}
    {stateEncoding : State ↪ List Bool}
    {program : α → WordOracleComp Op β}
    {typed : Caller → Q → StateT State (WordOracleComp External) R}
    {prepare : Caller → α} {initial : Caller → State} {resources : Caller → List Bool → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (hdecode : ComputableInPolyTime c.decodeQuery
      (encPair opEncoding encBits) (encOption queryEncoding))
    (hencodeReply : ComputableInPolyTime (fun p : Q × R => c.encodeReply p.1 p.2)
      (encPair queryEncoding replyEncoding) encBits)
    (htyped : IsOraclePPTOn
      (encPair input (encPair queryEncoding stateEncoding))
      (encPair replyEncoding stateEncoding)
      (fun p => typed p.1 p.2.1 p.2.2))
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : ComputableInPolyTime (fun pair => resources pair.1 pair.2)
      (encPair input encBits) encUnary)
    (hpreserve : ∀ a q state, invariant a state →
      ∀ result ∈ OracleComp.support (typed a q state),
        invariant a result.2 ∧
        (c.encodeReply q result.1).length ≤ resources a (c.encodeQuery q).2 ∧
        (stateEncoding result.2).length ≤
          (stateEncoding state).length + resources a (c.encodeQuery q).2) :
    IsOraclePPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          (c.wordOracle (typed a)))
        (program (prepare a))).run (initial a)) := by
  refine hprogram.run_interpret_preprocess_open hprepare
    (IsOraclePPTOn.wordOracle_state c defaultQuery hdecode hencodeReply htyped)
    hinitial invariant hinit hresources ?_
  intro a request state hinv result hresult
  unfold OracleCodec.wordOracle at hresult
  cases hd : c.decodeQuery request with
  | none =>
    simp only [hd] at hresult
    obtain rfl := OracleComp.eq_of_mem_supportWith_pure hresult
    exact ⟨hinv, Nat.zero_le _, Nat.le_add_right _ _⟩
  | some q =>
    simp only [hd] at hresult
    rw [show (c.encodeReply q <$> typed a q) state =
        ((c.encodeReply q <$> typed a q)).run state from rfl,
      StateT.run_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
    have hreq : c.encodeQuery q = request := (c.decodeQuery_eq_some_iff request q).mp hd
    rw [← hreq]
    exact hpreserve a q state hinv raw hraw

end Cslib.Probability
