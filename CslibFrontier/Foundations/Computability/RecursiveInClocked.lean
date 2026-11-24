/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Clocked
public import CslibFrontier.Foundations.Computability.RecursiveInUniform

/-!
# Oracle codes as clocked oracle programs

TODO
-/

@[expose] public section

namespace Cslib

/-- The interface of a single oracle `ℕ →. ℕ`: a query is a number and so is its answer. -/
abbrev natOracleSpec : OracleSpec ℕ := fun _ => ℕ

namespace OracleComp

variable {α : Type}

/-- The next move of a program over `natOracleSpec` once it has received the answers `rs` to its
first queries: its next query, or its result. Answers after the result are ignored. -/
def nextMove : OracleComp natOracleSpec α → List ℕ → ℕ ⊕ α
  | .pure a, _ => .inr a
  | .liftBind q _, [] => .inl q
  | .liftBind _ k, r :: rs => nextMove (k r) rs

/-- One step of running a program against `g`: ask its next query and append the answer, or
stay put once the program has a result. -/
def stepReplies (g : ℕ →. ℕ) (T : OracleComp natOracleSpec α) (rs : List ℕ) : Part (List ℕ) :=
  match nextMove T rs with
  | .inl q => (g q).map (rs ++ [·])
  | .inr _ => Part.some rs

/-- The answers `T` has received from `g` after `t` steps. -/
def replies (g : ℕ →. ℕ) (T : OracleComp natOracleSpec α) : ℕ → Part (List ℕ)
  | 0 => Part.some []
  | t + 1 => (replies g T t).bind (stepReplies g T)

theorem replies_pure (g : ℕ →. ℕ) (a : α) :
    ∀ t, replies g (.pure a : OracleComp natOracleSpec α) t = Part.some []
  | 0 => rfl
  | t + 1 => by rw [replies, replies_pure g a t, Part.bind_some]; rfl

theorem replies_liftBind (g : ℕ →. ℕ) (q : ℕ) (k : ℕ → OracleComp natOracleSpec α) :
    ∀ t, replies g (.liftBind q k) (t + 1) = (g q).bind fun r => (replies g (k r) t).map (r :: ·)
  | 0 => by
    simp only [replies, Part.bind_some, Part.map_some]
    simp [stepReplies, nextMove, Part.bind_some_eq_map]
  | t + 1 => by
    rw [replies, replies_liftBind g q k t, Part.bind_assoc]
    refine congrArg _ (funext fun r => ?_)
    rw [Part.bind_map, replies, Part.map_bind]
    refine congrArg _ (funext fun rs => ?_)
    simp only [stepReplies]
    change _ = (match nextMove (k r) rs with
      | .inl q => (g q).map (rs ++ [·])
      | .inr _ => Part.some rs).map (r :: ·)
    change (match nextMove (k r) rs with
      | .inl q => (g q).map (r :: rs ++ [·])
      | .inr _ => Part.some (r :: rs)) = _
    cases nextMove (k r) rs with
    | inl q => simp [Part.map_map, Function.comp_def]
    | inr _ => simp

/-- A program returns `a` against `g` iff some finite reply trace leads to the result `a`. -/
theorem mem_interpret_iff (g : ℕ →. ℕ) :
    ∀ (T : OracleComp natOracleSpec α) (a : α),
      a ∈ OracleComp.interpret g T ↔ ∃ t rs, rs ∈ replies g T t ∧ nextMove T rs = .inr a
  | .pure b, a => by
    change a ∈ Part.some b ↔ _
    simp only [nextMove, Sum.inr.injEq, Part.mem_some_iff, eq_comm (a := a)]
    exact ⟨fun h => ⟨0, [], Part.mem_some _, h⟩, fun ⟨_, _, _, h⟩ => h⟩
  | .liftBind q k, a => by
    change a ∈ (g q).bind (fun r => OracleComp.interpret g (k r)) ↔ _
    constructor
    · intro h
      obtain ⟨r, hr, h⟩ := Part.mem_bind_iff.1 h
      obtain ⟨t, rs, hrs, hn⟩ := (mem_interpret_iff g (k r) a).1 h
      refine ⟨t + 1, r :: rs, ?_, hn⟩
      rw [replies_liftBind]
      exact Part.mem_bind_iff.2 ⟨r, hr, Part.mem_map _ hrs⟩
    · rintro ⟨t, rs, hrs, hn⟩
      cases t with
      | zero =>
        obtain rfl := Part.mem_some_iff.1 hrs
        simp [nextMove] at hn
      | succ t =>
        rw [replies_liftBind] at hrs
        obtain ⟨r, hr, hrs⟩ := Part.mem_bind_iff.1 hrs
        obtain ⟨rs', hrs', rfl⟩ := (Part.mem_map_iff _).1 hrs
        exact Part.mem_bind_iff.2 ⟨r, hr, (mem_interpret_iff g (k r) a).2 ⟨t, rs', hrs', hn⟩⟩

theorem replies_dom_of_le {g : ℕ →. ℕ} {T : OracleComp natOracleSpec α} {m : ℕ} :
    ∀ {t}, (replies g T t).Dom → m ≤ t → (replies g T m).Dom
  | 0, h, hm => by rwa [Nat.le_zero.1 hm]
  | t + 1, h, hm => by
    rcases Nat.eq_or_lt_of_le hm with rfl | hm
    · exact h
    · exact replies_dom_of_le (Part.Dom.of_bind h) (Nat.lt_succ_iff.1 hm)

/-- Running a program against `g` iterates `stepReplies` up to the first step whose next move is
a result, and returns that result. -/
theorem interpret_eq_rfind [Inhabited α] (g : ℕ →. ℕ) (T : OracleComp natOracleSpec α) :
    OracleComp.interpret g T =
      (Nat.rfind fun t => (replies g T t).map fun rs => (nextMove T rs).isRight).bind fun t =>
        (replies g T t).map fun rs => (nextMove T rs).elim (fun _ => default) id := by
  ext a
  rw [Part.mem_bind_iff]
  constructor
  · intro ha
    obtain ⟨t, rs, hrs, hn⟩ := (mem_interpret_iff g T a).1 ha
    have hex : ∃ t, ∃ rs ∈ replies g T t, (nextMove T rs).isRight := ⟨t, rs, hrs, by simp [hn]⟩
    classical
    obtain ⟨rs₀, hrs₀, hn₀⟩ := Nat.find_spec hex
    have hdom : ∀ m < Nat.find hex, (replies g T m).Dom := fun m hm =>
      replies_dom_of_le hrs₀.fst hm.le
    refine ⟨Nat.find hex, Nat.mem_rfind.2 ⟨(Part.mem_map_iff _).2 ⟨rs₀, hrs₀, hn₀⟩,
      fun {m} hm => ?_⟩, ?_⟩
    · refine (Part.mem_map_iff _).2 ⟨(replies g T m).get (hdom m hm), Part.get_mem _, ?_⟩
      simpa using fun h => Nat.find_min hex hm ⟨_, Part.get_mem _, h⟩
    · obtain ⟨b, hb⟩ : ∃ b, nextMove T rs₀ = .inr b := by
        cases h : nextMove T rs₀ <;> simp_all
      have hb' := (mem_interpret_iff g T b).2 ⟨_, rs₀, hrs₀, hb⟩
      obtain rfl := Part.mem_unique ha hb'
      exact (Part.mem_map_iff _).2 ⟨rs₀, hrs₀, by simp [hb]⟩
  · rintro ⟨t, ht, ha⟩
    obtain ⟨rs, hrs, hfl⟩ := (Part.mem_map_iff _).1 (Nat.rfind_spec ht)
    obtain ⟨rs', hrs', rfl⟩ := (Part.mem_map_iff _).1 ha
    obtain rfl := Part.mem_unique hrs hrs'
    obtain ⟨b, hb⟩ : ∃ b, nextMove T rs = .inr b := by
      cases h : nextMove T rs <;> simp_all
    exact (mem_interpret_iff g T _).2 ⟨t, rs, hrs, by simp [hb]⟩

end OracleComp

namespace ClockedComp

open Nat.RecursiveIn.Code (HasUniformCode)

/-- The dialogue of a family of clocked programs on natural numbers: the next move of the program
for input `n` run with fuel `k`, after it has received the answers `rs`. A family whose dialogue
is computable is an oracle machine in the sense of Kleene: its control is computable, and only the
answers to its queries come from the oracle. -/
def dialogue (P : ℕ → ClockedComp natOracleSpec ℕ) (x : (ℕ × ℕ) × List ℕ) : ℕ ⊕ Option ℕ :=
  OracleComp.nextMove ((P x.1.1) x.1.2).run x.2

section Compile

variable {P : ℕ → ClockedComp natOracleSpec ℕ}

private abbrev State := (ℕ × ℕ) × List ℕ

private def decodeState (s : ℕ) : State := (Encodable.decode s).getD default

private theorem computable_decodeState : Computable decodeState :=
  Computable.option_getD Primrec.decode.to_comp (Computable.const _)

private theorem decodeState_encode (x : State) : decodeState (Encodable.encode x) = x := by
  simp only [decodeState, Encodable.encodek, Option.getD_some]

/-- The run of input and fuel `nk`, without the reader layer. -/
private abbrev run (P : ℕ → ClockedComp natOracleSpec ℕ) (nk : ℕ) : OracleComp natOracleSpec (Option ℕ) :=
  ((P nk.unpair.1) nk.unpair.2).run

/-- The encoded state of the run `nk` after receiving `rs`. -/
private abbrev enc (nk : ℕ) (rs : List ℕ) : ℕ :=
  Encodable.encode (((nk.unpair.1, nk.unpair.2), rs) : State)

private theorem computable_move (hP : Computable (dialogue P)) : Computable fun s => dialogue P (decodeState s) :=
  hP.comp computable_decodeState

/-- `0` once the program has a result, `1` while it still queries. -/
private def busy (P : ℕ → ClockedComp natOracleSpec ℕ) (s : ℕ) : ℕ :=
  Sum.elim (fun _ => 1) (fun _ => 0) (dialogue P (decodeState s))

private def nextQuery (P : ℕ → ClockedComp natOracleSpec ℕ) (s : ℕ) : ℕ :=
  Sum.elim id (fun _ => 0) (dialogue P (decodeState s))

private def push (p : ℕ) : ℕ :=
  Encodable.encode ((decodeState p.unpair.1).1, (decodeState p.unpair.1).2 ++ [p.unpair.2])

private def output (P : ℕ → ClockedComp natOracleSpec ℕ) (s : ℕ) : ℕ :=
  Encodable.encode (Sum.elim (fun _ => (none : Option ℕ)) id (dialogue P (decodeState s)))

private theorem computable_busy (hP : Computable (dialogue P)) : Computable (busy P) :=
  Computable.sumCasesOn (computable_move hP) (Computable.const 1).to₂ (Computable.const 0).to₂

private theorem computable_nextQuery (hP : Computable (dialogue P)) : Computable (nextQuery P) :=
  Computable.sumCasesOn (computable_move hP) Computable.snd.to₂ (Computable.const 0).to₂

private theorem computable_push : Computable push := by
  have hd : Computable fun p : ℕ => decodeState p.unpair.1 :=
    computable_decodeState.comp (Computable.fst.comp Primrec.unpair.to_comp)
  exact Computable.encode.comp ((Computable.fst.comp hd).pair
    (Computable.list_concat.comp (Computable.snd.comp hd)
      (Computable.snd.comp Primrec.unpair.to_comp)))

private theorem computable_output (hP : Computable (dialogue P)) : Computable (output P) :=
  Computable.encode.comp (Computable.sumCasesOn (computable_move hP) (Computable.const none).to₂
    Computable.snd.to₂)

private theorem busy_enc (nk : ℕ) (rs : List ℕ) :
    busy P (enc nk rs) = Sum.elim (fun _ => 1) (fun _ => 0) (OracleComp.nextMove (run P nk) rs) := by
  simp only [busy, enc, decodeState_encode, dialogue, run]

private theorem nextQuery_enc (nk : ℕ) (rs : List ℕ) :
    nextQuery P (enc nk rs) = Sum.elim id (fun _ => 0) (OracleComp.nextMove (run P nk) rs) := by
  simp only [nextQuery, enc, decodeState_encode, dialogue, run]

private theorem output_enc (nk : ℕ) (rs : List ℕ) :
    output P (enc nk rs) = Encodable.encode
      ((OracleComp.nextMove (run P nk) rs).elim (fun _ => default) id) := by
  simp only [output, enc, decodeState_encode, dialogue, run]
  cases OracleComp.nextMove ((P nk.unpair.1) nk.unpair.2).run rs <;> rfl

private theorem push_enc (nk : ℕ) (rs : List ℕ) (r : ℕ) :
    push (Nat.pair (enc nk rs) r) = enc nk (rs ++ [r]) := by
  simp only [push, enc, Nat.unpair_pair, decodeState_encode]

/-- One step of the encoded run. -/
private theorem hasUniformCode_step (hP : Computable (dialogue P)) : HasUniformCode id fun g s =>
    if busy P s = 0 then Part.some s else (g (nextQuery P s)).map fun r => push (Nat.pair s r) := by
  refine (HasUniformCode.ite (computable_busy hP)
    ((HasUniformCode.of_computable computable_push).comp
      ((HasUniformCode.of_primrec Nat.Primrec.id).pair
        ((HasUniformCode.oracle (o := id)).comp
          (HasUniformCode.of_computable (computable_nextQuery hP)))))).of_eq fun g s => ?_
  split_ifs
  · rfl
  · simp [Seq.seq, Part.bind_some_eq_map, Part.map_map, Function.comp_def]
    exact congrArg _ (Part.bind_some _ _)

private theorem step_enc (g : ℕ →. ℕ) (nk : ℕ) (rs : List ℕ) :
    (if busy P (enc nk rs) = 0 then Part.some (enc nk rs)
      else (g (nextQuery P (enc nk rs))).map fun r => push (Nat.pair (enc nk rs) r)) =
      (OracleComp.stepReplies g (run P nk) rs).map (enc nk) := by
  rw [busy_enc, nextQuery_enc, OracleComp.stepReplies]
  cases OracleComp.nextMove (run P nk) rs with
  | inl q => simp only [Part.map_map, Function.comp_def, push_enc]; rfl
  | inr _ => simp

/-- The encoded state of the run `p.unpair.1` after `p.unpair.2` steps. -/
private theorem hasUniformCode_replies (hP : Computable (dialogue P)) : HasUniformCode id fun g p =>
    (OracleComp.replies g (run P p.unpair.1) p.unpair.2).map (enc p.unpair.1) := by
  have hbase : Computable fun nk => enc nk [] :=
    Computable.encode.comp (Primrec.unpair.to_comp.pair (Computable.const []))
  have hrr : Nat.Primrec fun p => p.unpair.2.unpair.2 := Nat.Primrec.right.comp Nat.Primrec.right
  refine (HasUniformCode.prec (HasUniformCode.of_computable hbase)
    ((hasUniformCode_step hP).comp (HasUniformCode.of_primrec hrr))).of_eq fun g p => ?_
  rw [Nat.unpaired]
  induction p.unpair.2 with
  | zero => rfl
  | succ t ih =>
    simp only
    rw [ih, OracleComp.replies, Part.map_bind]
    change ((OracleComp.replies g (run P p.unpair.1) t).map (enc p.unpair.1)).bind _ = _
    rw [Part.bind_map]
    refine congrArg _ (funext fun rs => ?_)
    simp only [Nat.unpair_pair, ← step_enc]
    exact Part.bind_some _ _

/-- The first step at which the run `nk` has a result. -/
private theorem hasUniformCode_haltTime (hP : Computable (dialogue P)) :
    HasUniformCode id fun g nk => Nat.rfind fun t =>
      (OracleComp.replies g (run P nk) t).map fun rs =>
        (OracleComp.nextMove (run P nk) rs).isRight := by
  refine (HasUniformCode.rfind ((HasUniformCode.of_computable (computable_busy hP)).comp
    (hasUniformCode_replies hP))).of_eq fun g nk => ?_
  refine congrArg _ (funext fun t => ?_)
  simp only [Nat.unpair_pair]
  change Part.map _ (((OracleComp.replies g (run P nk) t).map (enc nk)).bind _) = _
  rw [Part.bind_map]
  simp only [Function.comp_def, busy_enc, Part.bind_some_eq_map, Part.map_map]
  refine congrArg (Part.map · _) (funext fun rs => ?_)
  cases OracleComp.nextMove (run P nk) rs <;> rfl

/-- The encoded result of the run with fuel `nk.unpair.2` on input `nk.unpair.1`. -/
private theorem hasUniformCode_attempt (hP : Computable (dialogue P)) :
    HasUniformCode id fun g nk => (attempt g (P nk.unpair.1) nk.unpair.2).map Encodable.encode := by
  refine ((HasUniformCode.of_computable (computable_output hP)).comp
    ((hasUniformCode_replies hP).comp ((HasUniformCode.of_primrec Nat.Primrec.id).pair
      (hasUniformCode_haltTime hP)))).of_eq fun g nk => ?_
  change _ = (OracleComp.interpret g (run P nk)).map Encodable.encode
  rw [OracleComp.interpret_eq_rfind, Part.map_bind]
  simp only [Seq.seq, id_eq, Part.bind_eq_bind, Part.bind_map, Part.bind_assoc, Function.comp_def,
    Part.bind_some_eq_map, Part.map_map]
  change Part.map (output P) ((Part.some (Nat.pair nk)).bind _) = _
  simp only [Part.bind_some, Nat.unpair_pair, Part.map_bind, Part.map_map, Function.comp_def,
    output_enc]

/-- The least fuel for which the run on input `n` finishes. -/
private theorem hasUniformCode_fuel (hP : Computable (dialogue P)) :
    HasUniformCode id fun g n => Nat.rfind fun k => (attempt g (P n) k).map Option.isSome := by
  have hsub : Computable fun e : ℕ => 1 - e :=
    (Primrec₂.to_comp Primrec.nat_sub).comp (Computable.const 1) Computable.id
  refine (HasUniformCode.rfind ((HasUniformCode.of_computable hsub).comp
    (hasUniformCode_attempt hP))).of_eq fun g n => ?_
  refine congrArg _ (funext fun k => ?_)
  simp only [Nat.unpair_pair]
  change Part.map _ (((attempt g (P n) k).map Encodable.encode).bind _) = _
  rw [Part.bind_map]
  simp only [Function.comp_def, Part.bind_some_eq_map, Part.map_map]
  refine congrArg (Part.map · _) (funext fun r => ?_)
  cases r <;> simp [Encodable.encode_some, Encodable.encode_nat]

private theorem bind_rfind_congr {α : Type} {p : ℕ →. Bool} {f f' : ℕ → Part α}
    (h : ∀ k ∈ Nat.rfind p, f k = f' k) : (Nat.rfind p).bind f = (Nat.rfind p).bind f' := by
  ext a
  simp only [Part.mem_bind_iff]
  exact ⟨fun ⟨k, hk, ha⟩ => ⟨k, hk, h k hk ▸ ha⟩, fun ⟨k, hk, ha⟩ => ⟨k, hk, (h k hk).symm ▸ ha⟩⟩

/-- **Program to code.** A family of clocked programs whose dialogue is computable is computed by
a single oracle code, relative to every partial oracle. The code follows the definition of
`ClockedComp.eval`: it searches for the least fuel that finishes, running each fuel by
iterating the dialogue and querying the oracle at each requested point. -/
theorem exists_code_eval (hP : Computable (dialogue P)) :
    ∃ c : Nat.RecursiveIn.Code, ∀ g : ℕ →. ℕ, c.eval g = fun n => eval g (P n) := by
  have hpred : Computable fun e : ℕ => e - 1 :=
    (Primrec₂.to_comp Primrec.nat_sub).comp Computable.id (Computable.const 1)
  obtain ⟨c, hc⟩ := ((HasUniformCode.of_computable hpred).comp ((hasUniformCode_attempt hP).comp
    ((HasUniformCode.of_primrec Nat.Primrec.id).pair (hasUniformCode_fuel hP)))).of_eq
      (G := fun g n => eval g (P n)) fun g n => by
        simp only [Seq.seq, id_eq, Part.bind_eq_bind, Part.bind_map, Part.bind_assoc,
          Part.bind_some_eq_map]
        change Part.map _ ((Part.some (Nat.pair n)).bind _) = _
        simp only [Part.bind_some, Nat.unpair_pair, Part.map_bind, Part.map_map,
          Function.comp_def]
        change _ = (Nat.rfind fun k => (attempt g (P n) k).map Option.isSome).bind fun k =>
          (attempt g (P n) k).bind fun r => (r : Part ℕ)
        refine bind_rfind_congr fun k hk => ?_
        obtain ⟨r, hr, hs⟩ := (Part.mem_map_iff _).1 (Nat.rfind_spec hk)
        obtain ⟨b, rfl⟩ := Option.isSome_iff_exists.1 hs
        rw [Part.eq_some_iff.2 hr, Part.map_some, Part.bind_some]
        simp [Encodable.encode_some, Encodable.encode_nat]
  exact ⟨c, hc⟩

/-- Every family of clocked programs with computable dialogue computes a function recursive in
the oracle it queries. -/
theorem recursiveIn_eval (hP : Computable (dialogue P)) (g : ℕ →. ℕ) :
    Nat.RecursiveIn {g} fun n => eval g (P n) := by
  obtain ⟨c, hc⟩ := exists_code_eval hP
  exact Nat.RecursiveIn.Code.exists_code.2 ⟨c, hc g⟩

end Compile

end ClockedComp

end Cslib

open Cslib

namespace Nat.RecursiveIn.Code

/-- Compile an oracle code to a clocked program querying the oracle, constructor by constructor:
composition is `bind`, primitive recursion is Lean recursion on the counter, and unbounded search
is `ClockedComp.rfind`. -/
def toClocked : Code → ℕ → ClockedComp natOracleSpec ℕ
  | zero => fun _ => pure 0
  | succ => fun n => pure (n + 1)
  | left => fun n => pure n.unpair.1
  | right => fun n => pure n.unpair.2
  | oracle => fun n => ClockedComp.query n
  | pair cf cg => fun n => do
      let a ← toClocked cf n
      let b ← toClocked cg n
      pure (Nat.pair a b)
  | comp cf cg => fun n => toClocked cg n >>= toClocked cf
  | prec cf cg => Nat.unpaired fun a m =>
      m.rec (toClocked cf a) fun y ih => ih >>= fun i => toClocked cg (Nat.pair a (Nat.pair y i))
  | rfind' cf => Nat.unpaired fun a m =>
      (· + m) <$> ClockedComp.rfind fun i =>
        (fun x => decide (x = 0)) <$> toClocked cf (Nat.pair a (i + m))

/-- The compiled program is stable against every partial oracle and computes the code. -/
theorem stable_toClocked_and_eval (g : ℕ →. ℕ) :
    ∀ (c : Code) (n : ℕ), ClockedComp.Stable g (c.toClocked n) ∧
      ClockedComp.eval g (c.toClocked n) = c.eval g n
  | zero, n => ⟨.pure _, ClockedComp.eval_pure g 0⟩
  | succ, n => ⟨.pure _, ClockedComp.eval_pure g _⟩
  | left, n => ⟨.pure _, ClockedComp.eval_pure g _⟩
  | right, n => ⟨.pure _, ClockedComp.eval_pure g _⟩
  | oracle, n => ⟨.query n, ClockedComp.eval_query g n⟩
  | pair cf cg, n => by
    obtain ⟨hf, ef⟩ := stable_toClocked_and_eval g cf n
    obtain ⟨hg, eg⟩ := stable_toClocked_and_eval g cg n
    refine ⟨hf.bind fun _ => hg.bind fun _ => .pure _, ?_⟩
    simp only [toClocked]
    rw [ClockedComp.eval_bind g hf fun _ => hg.bind fun _ => .pure _]
    simp only [ClockedComp.eval_bind g hg fun _ => .pure _, ClockedComp.eval_pure g, ef, eg, eval]
    simp only [seq_eq_bind_map, map_eq_pure_bind, bind_assoc, pure_bind]
    rfl
  | comp cf cg, n => by
    obtain ⟨hg, eg⟩ := stable_toClocked_and_eval g cg n
    have hf := fun a => stable_toClocked_and_eval g cf a
    refine ⟨hg.bind fun a => (hf a).1, ?_⟩
    simp only [toClocked]
    rw [ClockedComp.eval_bind g hg fun a => (hf a).1, eg, eval]
    simp only [(hf _).2]
    rfl
  | prec cf cg, n => by
    have hf := stable_toClocked_and_eval g cf
    have hg := stable_toClocked_and_eval g cg
    simp only [toClocked, eval, Nat.unpaired]
    induction n.unpair.2 with
    | zero => exact hf _
    | succ m ih =>
      obtain ⟨hs, he⟩ := ih
      refine ⟨hs.bind fun _ => (hg _).1, ?_⟩
      rw [ClockedComp.eval_bind g hs fun _ => (hg _).1, he]
      simp only [(hg _).2]
      rfl
  | rfind' cf, n => by
    have hf := stable_toClocked_and_eval g cf
    simp only [toClocked, eval, Nat.unpaired]
    have hp : ∀ i, ClockedComp.Stable g ((fun x => decide (x = 0)) <$>
        toClocked cf (Nat.pair n.unpair.1 (i + n.unpair.2))) := fun i => (hf _).1.map _
    refine ⟨(ClockedComp.Stable.rfind hp).map _, ?_⟩
    rw [ClockedComp.eval_map g (.rfind hp), ClockedComp.eval_rfind g hp]
    simp only [ClockedComp.eval_map g (hf _).1, (hf _).2]
    rfl

end Nat.RecursiveIn.Code
