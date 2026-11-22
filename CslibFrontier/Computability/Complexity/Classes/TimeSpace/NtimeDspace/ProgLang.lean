/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.StructuredProgram

/-!
# A verified functional language for counter programs

`Prog` is a first-order functional language over natural numbers: constants,
variables (de Bruijn indices into an environment), arithmetic, bit tests,
comparisons, input bits, conditionals, `let`, and bounded folds. Its meaning is
`eval`. `compile` translates a term into a structured counter program that
keeps the environment and all intermediate values in registers, allocated by a
stack discipline above a `fresh` index.

`compile_correct` is the only machine-level fact needed for programs written in
this language: executing the compiled term writes `eval` into the destination
register, changes no register below `fresh` except the destination, and keeps
every register at most `B`, provided every value arising in the evaluation is
at most `B` (`Bounded`). Programs are then verified by reasoning about `eval`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgLang

open _root_.Turing _root_.Turing.CounterProgram Structured

/-- Terms. `fold n init body` iterates `body` for `i < n`, with the accumulator
at index `0` and the counter at index `1` of the extended environment. -/
inductive Prog : Type where
  | const (k : ℕ)
  | var (i : ℕ)
  | add (a b : Prog)
  | sub (a b : Prog)
  | mul (a b : Prog)
  | div (a b : Prog)
  | mod (a b : Prog)
  | bit (a i : Prog)
  | lt (a b : Prog)
  | input (a : Prog)
  | ite (c t e : Prog)
  | letIn (a body : Prog)
  | fold (n init body : Prog)

namespace Prog

/-- The input bit at a position: `1`, `0`, or `2` past the end. -/
def inputValue (w : List Bool) (position : ℕ) : ℕ :=
  match w[position]? with
  | some true => 1
  | some false => 0
  | none => 2

/-- The meaning of a term on input `w` in environment `env`. -/
def eval (w : List Bool) : Prog → List ℕ → ℕ
  | const k, _ => k
  | var i, env => env.getD i 0
  | add a b, env => eval w a env + eval w b env
  | sub a b, env => eval w a env - eval w b env
  | mul a b, env => eval w a env * eval w b env
  | div a b, env => eval w a env / eval w b env
  | mod a b, env => eval w a env % eval w b env
  | bit a i, env => ((eval w a env).testBit (eval w i env)).toNat
  | lt a b, env => if eval w a env < eval w b env then 1 else 0
  | input a, env => inputValue w (eval w a env)
  | ite c t e, env => if 0 < eval w c env then eval w t env else eval w e env
  | letIn a body, env => eval w body (eval w a env :: env)
  | fold n init body, env =>
      (List.range (eval w n env)).foldl (fun acc i => eval w body (acc :: i :: env))
        (eval w init env)

/-- The accumulator after `k` iterations of a fold. -/
def foldAcc (w : List Bool) (body : Prog) (env : List ℕ) (init : ℕ) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i => eval w body (acc :: i :: env)) init

theorem foldAcc_succ (w : List Bool) (body : Prog) (env : List ℕ) (init k : ℕ) :
    foldAcc w body env init (k + 1) = eval w body (foldAcc w body env init k :: k :: env) := by
  simp [foldAcc, List.range_succ, List.foldl_append]

theorem eval_fold (w : List Bool) (n init body : Prog) (env : List ℕ) :
    eval w (fold n init body) env = foldAcc w body env (eval w init env) (eval w n env) := rfl

/-- Every value arising in the evaluation is at most `B`. -/
def Bounded (w : List Bool) (B : ℕ) : Prog → List ℕ → Prop
  | const k, _ => k ≤ B
  | var _, _ => True
  | add a b, env => Bounded w B a env ∧ Bounded w B b env ∧ eval w (add a b) env ≤ B
  | sub a b, env => Bounded w B a env ∧ Bounded w B b env
  | mul a b, env => Bounded w B a env ∧ Bounded w B b env ∧ eval w (mul a b) env ≤ B
  | div a b, env => Bounded w B a env ∧ Bounded w B b env
  | mod a b, env => Bounded w B a env ∧ Bounded w B b env
  | bit a i, env => Bounded w B a env ∧ Bounded w B i env
  | lt a b, env => Bounded w B a env ∧ Bounded w B b env
  | input a, env => Bounded w B a env
  | ite c t e, env => Bounded w B c env ∧
      (if 0 < eval w c env then Bounded w B t env else Bounded w B e env)
  | letIn a body, env => Bounded w B a env ∧ Bounded w B body (eval w a env :: env)
  | fold n init body, env => Bounded w B n env ∧ Bounded w B init env ∧
      eval w n env ≤ B ∧ ∀ k < eval w n env,
        Bounded w B body (foldAcc w body env (eval w init env) k :: k :: env)

/-- Registers used above `fresh`. -/
def span : Prog → ℕ
  | const _ | var _ => 0
  | add a b | sub a b | mul a b | div a b | mod a b | bit a b | lt a b =>
      max (span a + 1) (span b + 2)
  | input a => span a + 1
  | ite c t e => max (span c + 1) (max (span t) (span e) + 1)
  | letIn a body => max (span a + 1) (span body + 1)
  | fold n init body => max (span n + 1) (max (span init + 2) (span body + 4))

/-- The register holding variable `i`, or the constant zero for a variable
outside the environment. -/
def varExpr (envRegs : List ℕ) (i : ℕ) : Expr :=
  if h : i < envRegs.length then .reg envRegs[i] else .const 0

/-- A binary operation: both operands in scratch registers, then one assignment. -/
def binaryStmt (op : Expr → Expr → Expr) (sa sb : Stmt) (dst f : ℕ) : Stmt :=
  .seq sa (.seq sb (.assign dst (op (.reg f) (.reg (f + 1)))))

/-- Compile into register `dst`, with the environment in `envRegs` and scratch
registers from `fresh` on. -/
def compile : Prog → List ℕ → ℕ → ℕ → Stmt
  | const k, _, dst, _ => .assign dst (.const k)
  | var i, envRegs, dst, _ => .assign dst (varExpr envRegs i)
  | add a b, envRegs, dst, f =>
      binaryStmt .add (compile a envRegs f (f + 1)) (compile b envRegs (f + 1) (f + 2)) dst f
  | sub a b, envRegs, dst, f =>
      binaryStmt .sub (compile a envRegs f (f + 1)) (compile b envRegs (f + 1) (f + 2)) dst f
  | mul a b, envRegs, dst, f =>
      binaryStmt .mul (compile a envRegs f (f + 1)) (compile b envRegs (f + 1) (f + 2)) dst f
  | div a b, envRegs, dst, f =>
      binaryStmt .div (compile a envRegs f (f + 1)) (compile b envRegs (f + 1) (f + 2)) dst f
  | mod a b, envRegs, dst, f =>
      binaryStmt .mod (compile a envRegs f (f + 1)) (compile b envRegs (f + 1) (f + 2)) dst f
  | bit a i, envRegs, dst, f =>
      binaryStmt .bit (compile a envRegs f (f + 1)) (compile i envRegs (f + 1) (f + 2)) dst f
  | lt a b, envRegs, dst, f =>
      .seq (compile a envRegs f (f + 1)) (.seq (compile b envRegs (f + 1) (f + 2))
        (.ite (.reg f) (.reg (f + 1)) (.assign dst (.const 1)) (.assign dst (.const 0))))
  | input a, envRegs, dst, f =>
      .seq (compile a envRegs f (f + 1))
        (.read (.reg f) (.assign dst (.const 1)) (.assign dst (.const 0)) (.assign dst (.const 2)))
  | ite c t e, envRegs, dst, f =>
      .seq (compile c envRegs f (f + 1))
        (.ite (.const 0) (.reg f) (compile t envRegs dst (f + 1)) (compile e envRegs dst (f + 1)))
  | letIn a body, envRegs, dst, f =>
      .seq (compile a envRegs f (f + 1)) (compile body (f :: envRegs) dst (f + 1))
  | fold n init body, envRegs, dst, f =>
      .seq (compile n envRegs f (f + 1)) (.seq (compile init envRegs (f + 1) (f + 2))
        (.seq (.assign (f + 2) (.const 0))
          (.seq (.loop (.reg (f + 2)) (.reg f)
              (.seq (compile body ((f + 1) :: (f + 2) :: envRegs) (f + 3) (f + 4))
                (.seq (.assign (f + 1) (.reg (f + 3)))
                  (.assign (f + 2) (.add (.reg (f + 2)) (.const 1))))))
            (.assign dst (.reg (f + 1))))))

end Prog

/-! ### Register lists -/

section Registers

theorem getD_set_self {l : List ℕ} {j : ℕ} (v : ℕ) (h : j < l.length) :
    (l.set j v).getD j 0 = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_self h]

theorem getD_set_ne {l : List ℕ} {i j : ℕ} (v : ℕ) (h : i ≠ j) :
    (l.set j v).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem forall_set_le {l : List ℕ} {B j v : ℕ} (hl : ∀ x ∈ l, x ≤ B) (hv : v ≤ B) :
    ∀ x ∈ l.set j v, x ≤ B := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with h | h
  · exact hl x h
  · exact h ▸ hv

theorem getD_le {l : List ℕ} {B : ℕ} (hl : ∀ x ∈ l, x ≤ B) (i : ℕ) : l.getD i 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simp
  | some x => simpa using hl x (List.mem_of_getElem? h)

end Registers

/-! ### Correctness of the compiler -/

section Correctness

open Prog

variable (w : List Bool) (B : ℕ)

/-- All registers are at most `B`. -/
def LeB (r : List ℕ) : Prop := ∀ x ∈ r, x ≤ B

/-- The environment sits in registers below `f`. -/
def EnvOK (envRegs env regs : List ℕ) (f : ℕ) : Prop :=
  envRegs.length = env.length ∧
    ∀ i (h : i < envRegs.length), envRegs[i] < f ∧ regs.getD envRegs[i] 0 = env.getD i 0

/-- The postcondition of a compiled term. -/
def Post (s : Stmt) (regs : List ℕ) (dst f v : ℕ) : Prop :=
  ∃ regs', Exec w (LeB B) s regs regs' ∧ regs'.length = regs.length ∧ regs'.getD dst 0 = v ∧
    (∀ j, j < f → j ≠ dst → regs'.getD j 0 = regs.getD j 0) ∧ LeB B regs'

variable {w B}

theorem EnvOK.mono {envRegs env regs : List ℕ} {f f' : ℕ} (h : EnvOK envRegs env regs f)
    (hf : f ≤ f') : EnvOK envRegs env regs f' :=
  ⟨h.1, fun i hi => ⟨(h.2 i hi).1.trans_le hf, (h.2 i hi).2⟩⟩

theorem EnvOK.frame {envRegs env regs regs' : List ℕ} {f d : ℕ} (h : EnvOK envRegs env regs f)
    (hd : f ≤ d) (frame : ∀ j, j < f → j ≠ d → regs'.getD j 0 = regs.getD j 0) :
    EnvOK envRegs env regs' f :=
  ⟨h.1, fun i hi => ⟨(h.2 i hi).1, by
    rw [frame _ (h.2 i hi).1 (by have := (h.2 i hi).1; omega)]; exact (h.2 i hi).2⟩⟩

theorem EnvOK.frame' {envRegs env regs regs' : List ℕ} {f f' d : ℕ} (h : EnvOK envRegs env regs f)
    (hd : f ≤ d) (hf' : f ≤ f')
    (frame : ∀ j, j < f' → j ≠ d → regs'.getD j 0 = regs.getD j 0) :
    EnvOK envRegs env regs' f :=
  h.frame hd fun j hj hjd => frame j (hj.trans_le hf') hjd

theorem varExpr_eval {envRegs env regs : List ℕ} {f : ℕ} (h : EnvOK envRegs env regs f) (i : ℕ) :
    (varExpr envRegs i).eval regs = env.getD i 0 := by
  unfold varExpr
  split_ifs with hi
  · simpa using (h.2 i hi).2
  · have : env.length ≤ i := by rw [← h.1]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]

theorem assign_post {regs : List ℕ} {dst f : ℕ} {e : Expr} (hlen : dst < regs.length)
    (hreg : LeB B regs) (hv : e.eval regs ≤ B) :
    Post w B (.assign dst e) regs dst f (e.eval regs) :=
  ⟨regs.set dst (e.eval regs), .assign hreg, by simp, getD_set_self _ hlen,
    fun j _ hj => getD_set_ne _ hj, forall_set_le hreg hv⟩

/-- Sequencing two compiled pieces: the first into `f`, the second into `f+1`. -/
theorem binary_post (op : Expr → Expr → Expr) (opv : ℕ → ℕ → ℕ)
    (hop : ∀ (r : List ℕ) i j, (op (.reg i) (.reg j)).eval r = opv (r.getD i 0) (r.getD j 0))
    {sa sb : Stmt} {va vb : ℕ} {envRegs env regs : List ℕ} {dst f : ℕ}
    (hEnv : EnvOK envRegs env regs f) (hdst : dst < f) (hlen : f + 2 ≤ regs.length)
    (hreg : LeB B regs)
    (ha : ∀ r : List ℕ, EnvOK envRegs env r (f + 1) → r.length = regs.length → LeB B r →
      Post w B sa r f (f + 1) va)
    (hb : ∀ r : List ℕ, EnvOK envRegs env r (f + 2) → r.length = regs.length → LeB B r →
      Post w B sb r (f + 1) (f + 2) vb)
    (hv : va ≤ B → vb ≤ B → opv va vb ≤ B) :
    Post w B (binaryStmt op sa sb dst f) regs dst f (opv va vb) := by
  obtain ⟨r1, e1, l1, v1, fr1, b1⟩ := ha regs (hEnv.mono (by omega)) rfl hreg
  have env1 : EnvOK envRegs env r1 f := hEnv.frame' (le_refl f) (by omega) fr1
  obtain ⟨r2, e2, l2, v2, fr2, b2⟩ := hb r1 (env1.mono (by omega)) l1 b1
  have hf : r2.getD f 0 = va := by rw [fr2 f (by omega) (by omega), v1]
  have hval : (op (.reg f) (.reg (f + 1))).eval r2 = opv va vb := by rw [hop, hf, v2]
  have hva : va ≤ B := hf ▸ getD_le b2 f
  have hvb : vb ≤ B := v2 ▸ getD_le b2 (f + 1)
  refine ⟨r2.set dst (opv va vb), .seq e1 (.seq e2 (hval ▸ .assign b2)), by simp [l1, l2],
    getD_set_self _ (by omega), fun j hj hjd => ?_, forall_set_le b2 (hv hva hvb)⟩
  rw [getD_set_ne _ hjd, fr2 j (by omega) (by omega), fr1 j (by omega) (by omega)]

/-- The loop of a fold, by induction on the remaining iterations. -/
theorem loop_post (body : Stmt) (f n : ℕ) (acc : ℕ → ℕ) (Frame : List ℕ → Prop)
    (step : ∀ k < n, ∀ r : List ℕ, r.getD f 0 = n → r.getD (f + 1) 0 = acc k →
      r.getD (f + 2) 0 = k → Frame r → LeB B r →
      ∃ r', Exec w (LeB B) body r r' ∧ r'.getD f 0 = n ∧ r'.getD (f + 1) 0 = acc (k + 1) ∧
        r'.getD (f + 2) 0 = k + 1 ∧ Frame r' ∧ LeB B r') :
    ∀ m k (r : List ℕ), k + m = n → r.getD f 0 = n → r.getD (f + 1) 0 = acc k →
      r.getD (f + 2) 0 = k → Frame r → LeB B r →
      ∃ r', Exec w (LeB B) (.loop (.reg (f + 2)) (.reg f) body) r r' ∧
        r'.getD (f + 1) 0 = acc n ∧ Frame r' ∧ LeB B r' := by
  intro m
  induction m with
  | zero =>
    intro k r hk hn ha hi hF hb
    refine ⟨r, .loop_done hb (by simp only [Expr.eval_reg]; rw [hn, hi]; omega), ?_, hF, hb⟩
    rw [ha, show k = n by omega]
  | succ m ih =>
    intro k r hk hn ha hi hF hb
    obtain ⟨r', e', hn', ha', hi', hF', hb'⟩ := step k (by omega) r hn ha hi hF hb
    obtain ⟨r'', e'', ha'', hF'', hb''⟩ := ih (k + 1) r' (by omega) hn' ha' hi' hF' hb'
    exact ⟨r'', .loop_step hb (by simp only [Expr.eval_reg]; rw [hn, hi]; omega) e' hb' e'', ha'',
        hF'', hb''⟩

/-- **The compiler is correct.** -/
theorem compile_correct (hB : 2 ≤ B) : ∀ (P : Prog) (env envRegs : List ℕ) (dst f : ℕ)
    (regs : List ℕ), EnvOK envRegs env regs f → dst < f → f + P.span ≤ regs.length →
    LeB B regs → P.Bounded w B env → Post w B (P.compile envRegs dst f) regs dst f
        (P.eval w env) := by
  intro P
  induction P with
  | const k =>
    intro env envRegs dst f regs _ hdst _ hreg hbd
    exact assign_post (e := .const k) (by simp [span] at *; omega) hreg hbd
  | var i =>
    intro env envRegs dst f regs hEnv hdst _ hreg _
    have hle : (varExpr envRegs i).eval regs ≤ B := by
      unfold varExpr; split_ifs
      · exact getD_le hreg _
      · simp
    have := assign_post (w := w) (e := varExpr envRegs i) (f := f) (dst := dst)
      (by simp [span] at *; omega) hreg hle
    rw [varExpr_eval hEnv] at this
    exact this
  | add a b iha ihb =>
    intro env envRegs dst f regs hEnv hdst hlen hreg hbd
    simp only [span] at hlen
    have hm1 := le_max_left (a.span + 1) (b.span + 2)
    have hm2 := le_max_right (a.span + 1) (b.span + 2)
    exact binary_post .add (· + ·) (fun _ _ _ => by simp) hEnv hdst (by omega)
      hreg (fun r h1 h2 h3 => iha env envRegs f (f + 1) r h1 (by omega)
        (by omega) h3 hbd.1)
      (fun r h1 h2 h3 => ihb env envRegs (f + 1) (f + 2) r h1 (by omega)
        (by omega) h3 hbd.2.1) (fun _ _ => hbd.2.2)
  | sub a b iha ihb =>
    intro env envRegs dst f regs hEnv hdst hlen hreg hbd
    simp only [span] at hlen
    have hm1 := le_max_left (a.span + 1) (b.span + 2)
    have hm2 := le_max_right (a.span + 1) (b.span + 2)
    exact binary_post .sub (· - ·) (fun _ _ _ => by simp) hEnv hdst (by omega)
      hreg (fun r h1 h2 h3 => iha env envRegs f (f + 1) r h1 (by omega)
        (by omega) h3 hbd.1)
      (fun r h1 h2 h3 => ihb env envRegs (f + 1) (f + 2) r h1 (by omega)
        (by omega) h3 hbd.2) (fun ha _ => (Nat.sub_le _ _).trans ha)
  | mul a b iha ihb =>
    intro env envRegs dst f regs hEnv hdst hlen hreg hbd
    simp only [span] at hlen
    have hm1 := le_max_left (a.span + 1) (b.span + 2)
    have hm2 := le_max_right (a.span + 1) (b.span + 2)
    exact binary_post .mul (· * ·) (fun _ _ _ => by simp) hEnv hdst (by omega)
      hreg (fun r h1 h2 h3 => iha env envRegs f (f + 1) r h1 (by omega)
        (by omega) h3 hbd.1)
      (fun r h1 h2 h3 => ihb env envRegs (f + 1) (f + 2) r h1 (by omega)
        (by omega) h3 hbd.2.1) (fun _ _ => hbd.2.2)
  | div a b iha ihb =>
    intro env envRegs dst f regs hEnv hdst hlen hreg hbd
    simp only [span] at hlen
    have hm1 := le_max_left (a.span + 1) (b.span + 2)
    have hm2 := le_max_right (a.span + 1) (b.span + 2)
    exact binary_post .div (· / ·) (fun _ _ _ => by simp) hEnv hdst (by omega)
      hreg (fun r h1 h2 h3 => iha env envRegs f (f + 1) r h1 (by omega)
        (by omega) h3 hbd.1)
      (fun r h1 h2 h3 => ihb env envRegs (f + 1) (f + 2) r h1 (by omega)
        (by omega) h3 hbd.2) (fun ha _ => (Nat.div_le_self _ _).trans ha)
  | mod a b iha ihb =>
    intro env envRegs dst f regs hEnv hdst hlen hreg hbd
    simp only [span] at hlen
    have hm1 := le_max_left (a.span + 1) (b.span + 2)
    have hm2 := le_max_right (a.span + 1) (b.span + 2)
    exact binary_post .mod (· % ·) (fun _ _ _ => by simp) hEnv hdst (by omega)
      hreg (fun r h1 h2 h3 => iha env envRegs f (f + 1) r h1 (by omega)
        (by omega) h3 hbd.1)
      (fun r h1 h2 h3 => ihb env envRegs (f + 1) (f + 2) r h1 (by omega)
        (by omega) h3 hbd.2) (fun ha _ => (Nat.mod_le _ _).trans ha)
  | bit a i iha ihi =>
    intro env envRegs dst f regs hEnv hdst hlen hreg hbd
    simp only [span] at hlen
    have hm1 := le_max_left (a.span + 1) (i.span + 2)
    have hm2 := le_max_right (a.span + 1) (i.span + 2)
    exact binary_post .bit (fun x y => (x.testBit y).toNat) (fun _ _ _ => by simp) hEnv hdst
      (by omega)
      hreg (fun r h1 h2 h3 => iha env envRegs f (f + 1) r h1 (by omega)
        (by omega) h3 hbd.1)
      (fun r h1 h2 h3 => ihi env envRegs (f + 1) (f + 2) r h1 (by omega)
        (by omega) h3 hbd.2)
      (fun _ _ => (Bool.toNat_le _).trans (by omega))
  | lt a b iha ihb =>
    intro env envRegs dst f regs hEnv hdst hlen hreg hbd
    simp only [span] at hlen
    have hm1 := le_max_left (a.span + 1) (b.span + 2)
    have hm2 := le_max_right (a.span + 1) (b.span + 2)
    obtain ⟨r1, e1, l1, v1, fr1, b1⟩ := iha env envRegs f (f + 1) regs (hEnv.mono (by omega))
      (by omega) (by omega) hreg hbd.1
    have env1 : EnvOK envRegs env r1 f := hEnv.frame' (le_refl f) (by omega) fr1
    obtain ⟨r2, e2, l2, v2, fr2, b2⟩ := ihb env envRegs (f + 1) (f + 2) r1 (env1.mono (by omega))
      (by omega) (by omega) b1 hbd.2
    have hf : r2.getD f 0 = a.eval w env := by rw [fr2 f (by omega) (by omega), v1]
    have frame : ∀ v, ∀ j, j < f → j ≠ dst → (r2.set dst v).getD j 0 = regs.getD j 0 :=
      fun v j hj hjd => by
        rw [getD_set_ne _ hjd, fr2 j (by omega) (by omega), fr1 j (by omega) (by omega)]
    by_cases h : a.eval w env < b.eval w env
    · refine ⟨r2.set dst 1, .seq e1 (.seq e2
        (.ite_yes b2 (by simp only [Expr.eval_reg]; rw [hf, v2]; exact h) (.assign b2)
          (forall_set_le b2 (by omega)))), by simp [l1, l2], ?_, frame 1,
        forall_set_le b2 (by omega)⟩
      rw [getD_set_self _ (by omega)]; simp [Prog.eval, h]
    · refine ⟨r2.set dst 0, .seq e1 (.seq e2
        (.ite_no b2 (by simp only [Expr.eval_reg]; rw [hf, v2]; exact h) (.assign b2))),
        by simp [l1, l2], ?_, frame 0, forall_set_le b2 (by omega)⟩
      rw [getD_set_self _ (by omega)]; simp [Prog.eval, h]
  | input a iha =>
    intro env envRegs dst f regs hEnv hdst hlen hreg hbd
    simp only [span] at hlen
    obtain ⟨r1, e1, l1, v1, fr1, b1⟩ := iha env envRegs f (f + 1) regs (hEnv.mono (by omega))
      (by omega) (by omega) hreg hbd
    have frame : ∀ v, ∀ j, j < f → j ≠ dst → (r1.set dst v).getD j 0 = regs.getD j 0 :=
      fun v j hj hjd => by rw [getD_set_ne _ hjd, fr1 j (by omega) (by omega)]
    have hpos : (Expr.reg f).eval r1 = a.eval w env := by simp only [Expr.eval_reg]; exact v1
    rcases hw : w[a.eval w env]? with _ | ⟨_ | _⟩
    · refine ⟨r1.set dst 2, .seq e1 (.read_end b1 (by rw [hpos, hw]) (.assign b1)),
        by simp [l1], ?_, frame 2, forall_set_le b1 (by omega)⟩
      rw [getD_set_self _ (by omega)]; simp [Prog.eval, Prog.inputValue, hw]
    · refine ⟨r1.set dst 0, .seq e1 (.read_false b1 (by rw [hpos, hw]) (.assign b1)
          (forall_set_le b1 (by omega))), by simp [l1], ?_, frame 0, forall_set_le b1 (by omega)⟩
      rw [getD_set_self _ (by omega)]; simp [Prog.eval, Prog.inputValue, hw]
    · refine ⟨r1.set dst 1, .seq e1 (.read_true b1 (by rw [hpos, hw]) (.assign b1)
          (forall_set_le b1 (by omega))), by simp [l1], ?_, frame 1, forall_set_le b1 (by omega)⟩
      rw [getD_set_self _ (by omega)]; simp [Prog.eval, Prog.inputValue, hw]
  | ite c t e ihc iht ihe =>
    intro env envRegs dst f regs hEnv hdst hlen hreg hbd
    simp only [span] at hlen
    have hm1 := le_max_left (c.span + 1) (max t.span e.span + 1)
    have hm2 := le_max_right (c.span + 1) (max t.span e.span + 1)
    have hm3 := le_max_left t.span e.span
    have hm4 := le_max_right t.span e.span
    obtain ⟨r1, e1, l1, v1, fr1, b1⟩ := ihc env envRegs f (f + 1) regs (hEnv.mono (by omega))
      (by omega) (by omega) hreg hbd.1
    have env1 : EnvOK envRegs env r1 (f + 1) := (hEnv.frame' (le_refl f) (by omega) fr1).mono
      (by omega)
    have hc : (Expr.reg f).eval r1 = c.eval w env := by simp only [Expr.eval_reg]; exact v1
    by_cases h : 0 < c.eval w env
    · have hbt : t.Bounded w B env := by have := hbd.2; rw [if_pos h] at this; exact this
      obtain ⟨r2, e2, l2, v2, fr2, b2⟩ := iht env envRegs dst (f + 1) r1 env1 (by omega)
        (by omega) b1 hbt
      refine ⟨r2, .seq e1 (.ite_yes b1 (by simp [hc, h]) e2 b2), by simp [l1, l2], ?_,
        fun j hj hjd => by rw [fr2 j (by omega) hjd, fr1 j (by omega) (by omega)], b2⟩
      rw [v2]; simp [Prog.eval, h]
    · have hbe : e.Bounded w B env := by have := hbd.2; rw [if_neg h] at this; exact this
      obtain ⟨r2, e2, l2, v2, fr2, b2⟩ := ihe env envRegs dst (f + 1) r1 env1 (by omega)
        (by omega) b1 hbe
      refine ⟨r2, .seq e1 (.ite_no b1 (by simp [hc, h]) e2), by simp [l1, l2], ?_,
        fun j hj hjd => by rw [fr2 j (by omega) hjd, fr1 j (by omega) (by omega)], b2⟩
      rw [v2]; simp [Prog.eval, h]
  | letIn a body iha ihb =>
    intro env envRegs dst f regs hEnv hdst hlen hreg hbd
    simp only [span] at hlen
    have hm1 := le_max_left (a.span + 1) (body.span + 1)
    have hm2 := le_max_right (a.span + 1) (body.span + 1)
    obtain ⟨r1, e1, l1, v1, fr1, b1⟩ := iha env envRegs f (f + 1) regs (hEnv.mono (by omega))
      (by omega) (by omega) hreg hbd.1
    have env1 : EnvOK (f :: envRegs) (a.eval w env :: env) r1 (f + 1) := by
      refine ⟨by simp [hEnv.1], fun i hi => ?_⟩
      rcases i with _ | i
      · exact ⟨by simp, by simp only [List.getElem_cons_zero, List.getD_cons_zero]; exact v1⟩
      · have hi' : i < envRegs.length := by simpa using hi
        have := hEnv.2 i hi'
        refine ⟨by simp; omega, ?_⟩
        simp only [List.getElem_cons_succ, List.getD_cons_succ]
        rw [fr1 _ (by omega) (by omega)]; exact this.2
    obtain ⟨r2, e2, l2, v2, fr2, b2⟩ := ihb (a.eval w env :: env) (f :: envRegs) dst (f + 1) r1
      env1 (by omega) (by omega) b1 hbd.2
    exact ⟨r2, .seq e1 e2, by simp [l1, l2], v2,
      fun j hj hjd => by rw [fr2 j (by omega) hjd, fr1 j (by omega) (by omega)], b2⟩
  | fold n init body ihn ihi ihb =>
    intro env envRegs dst f regs hEnv hdst hlen hreg hbd
    simp only [span] at hlen
    have hm1 := le_max_left (n.span + 1) (max (init.span + 2) (body.span + 4))
    have hm2 := le_max_right (n.span + 1) (max (init.span + 2) (body.span + 4))
    have hm3 := le_max_left (init.span + 2) (body.span + 4)
    have hm4 := le_max_right (init.span + 2) (body.span + 4)
    obtain ⟨hbn, hbi, hnB, hbb⟩ := hbd
    obtain ⟨r1, e1, l1, v1, fr1, b1⟩ := ihn env envRegs f (f + 1) regs (hEnv.mono (by omega))
      (by omega) (by omega) hreg hbn
    have env1 : EnvOK envRegs env r1 f := hEnv.frame' (le_refl f) (by omega) fr1
    obtain ⟨r2, e2, l2, v2, fr2, b2⟩ := ihi env envRegs (f + 1) (f + 2) r1 (env1.mono (by omega))
      (by omega) (by omega) b1 hbi
    set vn := n.eval w env
    set acc := Prog.foldAcc w body env (init.eval w env)
    have b3 : LeB B (r2.set (f + 2) 0) := forall_set_le b2 (by omega)
    -- the frame kept by the loop: length, the bound `n`, and everything below `f`
    let Frame : List ℕ → Prop := fun r => r.length = regs.length ∧
      ∀ j, j < f → r.getD j 0 = regs.getD j 0
    have step : ∀ k < vn, ∀ r : List ℕ, r.getD f 0 = vn → r.getD (f + 1) 0 = acc k →
        r.getD (f + 2) 0 = k → Frame r → LeB B r →
        ∃ r', Exec w (LeB B) (.seq (body.compile ((f + 1) :: (f + 2) :: envRegs) (f + 3) (f + 4))
            (.seq (.assign (f + 1) (.reg (f + 3)))
              (.assign (f + 2) (.add (.reg (f + 2)) (.const 1))))) r r' ∧
          r'.getD f 0 = vn ∧ r'.getD (f + 1) 0 = acc (k + 1) ∧ r'.getD (f + 2) 0 = k + 1 ∧
          Frame r' ∧ LeB B r' := by
      intro k hk r hn ha hi hF hb
      have envB : EnvOK ((f + 1) :: (f + 2) :: envRegs) (acc k :: k :: env) r (f + 4) := by
        refine ⟨by simp [hEnv.1], fun i hi' => ?_⟩
        rcases i with _ | _ | i
        · exact ⟨by simp, by simp only [List.getElem_cons_zero, List.getD_cons_zero]; exact ha⟩
        · exact ⟨by simp, by
            simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ,
              List.getD_cons_zero]; exact hi⟩
        · have hi'' : i < envRegs.length := by simpa using hi'
          have := hEnv.2 i hi''
          refine ⟨by simp; omega, ?_⟩
          simp only [List.getElem_cons_succ, List.getD_cons_succ]
          rw [hF.2 _ this.1]; exact this.2
      obtain ⟨s1, x1, m1, w1, fs1, c1⟩ := ihb (acc k :: k :: env) ((f + 1) :: (f + 2) :: envRegs)
        (f + 3) (f + 4) r envB (by omega) (by omega) hb (hbb k hk)
      have hv1 : s1.getD (f + 3) 0 = acc (k + 1) := by
        rw [w1]; simp [acc, Prog.foldAcc_succ]
      have hacc : acc (k + 1) ≤ B := hv1 ▸ getD_le c1 (f + 3)
      set s2 := s1.set (f + 1) (acc (k + 1))
      have c2 : LeB B s2 := forall_set_le c1 hacc
      have ls2 : s2.length = regs.length := by
        rw [show s2 = s1.set (f + 1) (acc (k + 1)) from rfl, List.length_set, m1, hF.1]
      have hs2i : s2.getD (f + 2) 0 = k := by
        rw [getD_set_ne _ (by omega), fs1 _ (by omega) (by omega), hi]
      have hkB : k + 1 ≤ B := by omega
      have x2 : Exec w (LeB B) (.assign (f + 1) (.reg (f + 3))) s1 s2 := by
        have e : (Expr.reg (f + 3)).eval s1 = acc (k + 1) := by
          simp only [Expr.eval_reg]; exact hv1
        have := Exec.assign (w := w) (Inv := LeB B) (i := f + 1) (e := Expr.reg (f + 3)) c1
        rw [e] at this; exact this
      have x3 : Exec w (LeB B) (.assign (f + 2) (.add (.reg (f + 2)) (.const 1))) s2
          (s2.set (f + 2) (k + 1)) := by
        have e : (Expr.add (.reg (f + 2)) (.const 1)).eval s2 = k + 1 := by
          simp only [Expr.eval_add, Expr.eval_reg, Expr.eval_const]; rw [hs2i]
        have := Exec.assign (w := w) (Inv := LeB B) (i := f + 2)
          (e := Expr.add (.reg (f + 2)) (.const 1)) c2
        rw [e] at this; exact this
      refine ⟨s2.set (f + 2) (k + 1), .seq x1 (.seq x2 x3), ?_, ?_, ?_, ⟨?_, ?_⟩,
        forall_set_le c2 hkB⟩
      · rw [getD_set_ne _ (by omega), getD_set_ne _ (by omega), fs1 _ (by omega) (by omega), hn]
      · rw [getD_set_ne _ (by omega), getD_set_self _ (by rw [m1, hF.1]; omega)]
      · rw [getD_set_self _ (by rw [ls2]; omega)]
      · rw [List.length_set, ls2]
      · intro j hj
        rw [getD_set_ne _ (by omega), getD_set_ne _ (by omega), fs1 _ (by omega) (by omega),
          hF.2 j hj]
    have start_n : (r2.set (f + 2) 0).getD f 0 = vn := by
      rw [getD_set_ne _ (by omega), fr2 f (by omega) (by omega), v1]
    have start_a : (r2.set (f + 2) 0).getD (f + 1) 0 = acc 0 := by
      rw [getD_set_ne _ (by omega), v2]; simp [acc, Prog.foldAcc]
    have start_i : (r2.set (f + 2) 0).getD (f + 2) 0 = 0 := getD_set_self _ (by omega)
    have start_F : Frame (r2.set (f + 2) 0) := ⟨by simp [l1, l2], fun j hj => by
      rw [getD_set_ne _ (by omega), fr2 j (by omega) (by omega), fr1 j (by omega) (by omega)]⟩
    obtain ⟨r3, e3, a3, F3, b4⟩ := loop_post _ f vn acc Frame step vn 0 _ (by omega) start_n
      start_a start_i start_F b3
    have hval : (Expr.reg (f + 1)).eval r3 = (fold n init body).eval w env := by
      simp only [Expr.eval_reg]; rw [a3, Prog.eval_fold]
    refine ⟨r3.set dst ((fold n init body).eval w env),
      .seq e1 (.seq e2 (.seq (.assign b2) (.seq e3 (hval ▸ .assign b4)))),
      by simp [F3.1], getD_set_self _ (by rw [F3.1]; omega), fun j hj hjd => ?_,
      forall_set_le b4 (hval ▸ getD_le b4 (f + 1))⟩
    rw [getD_set_ne _ hjd, F3.2 j hj]

end Correctness

/-! ### Deciding with a term -/

section Decide

open Prog _root_.Turing.MultiTapeTM

/-- Runs preserve the number of registers, so an invariant may be weakened using
the length of the initial register list. -/
theorem exec_weaken {w : List Bool} {Inv Inv' : List ℕ → Prop} {s : Stmt} {r r' : List ℕ}
    (h : Exec w Inv s r r') :
    (∀ x, Inv x → x.length = r.length → Inv' x) → Exec w Inv' s r r' ∧ r'.length = r.length := by
  induction h with
  | skip r => intro _; exact ⟨.skip r, rfl⟩
  | assign hI => intro hw; exact ⟨.assign (hw _ hI rfl), by simp⟩
  | seq _ _ iha ihc =>
    intro hw
    obtain ⟨ea, la⟩ := iha hw
    obtain ⟨ec, lc⟩ := ihc fun x hx hl => hw x hx (hl.trans la)
    exact ⟨.seq ea ec, lc.trans la⟩
  | ite_yes hI hlt _ hI' ih =>
    intro hw
    obtain ⟨e, l⟩ := ih hw
    exact ⟨.ite_yes (hw _ hI rfl) hlt e (hw _ hI' l), l⟩
  | ite_no hI hlt _ ih =>
    intro hw
    obtain ⟨e, l⟩ := ih hw
    exact ⟨.ite_no (hw _ hI rfl) hlt e, l⟩
  | loop_step hI hlt _ hI' _ ihb ihl =>
    intro hw
    obtain ⟨eb, lb⟩ := ihb hw
    obtain ⟨el, ll⟩ := ihl fun x hx hl => hw x hx (hl.trans lb)
    exact ⟨.loop_step (hw _ hI rfl) hlt eb (hw _ hI' lb) el, ll.trans lb⟩
  | loop_done hI hlt => intro hw; exact ⟨.loop_done (hw _ hI rfl) hlt, rfl⟩
  | read_true hI hb _ hI' ih =>
    intro hw
    obtain ⟨e, l⟩ := ih hw
    exact ⟨.read_true (hw _ hI rfl) hb e (hw _ hI' l), l⟩
  | read_false hI hb _ hI' ih =>
    intro hw
    obtain ⟨e, l⟩ := ih hw
    exact ⟨.read_false (hw _ hI rfl) hb e (hw _ hI' l), l⟩
  | read_end hI hb _ ih =>
    intro hw
    obtain ⟨e, l⟩ := ih hw
    exact ⟨.read_end (hw _ hI rfl) hb e, l⟩

/-- Registers at most `2^K` have encoded length at most `(2K+3)` each. -/
theorem encList_le_of_LeB {K : ℕ} {r : List ℕ} (h : LeB (2 ^ K) r) :
    (encList encNat r).length ≤ r.length * (2 * K + 3) := by
  rw [length_encList]
  refine (List.sum_le_card_nsmul _ (2 * K + 3) fun x hx => ?_).trans (by simp)
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have hsize : (encNat y).length ≤ K + 1 := by
    rw [length_encNat_eq_size, Nat.size_le]
    exact (h y hy).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  omega

/-- **A term that decides `L` with values below `2^K` gives a decider** in
simultaneous time `2^(C*budget)` and space `C*budget`, when `K ≤ c*budget`. -/
theorem decidable_of_prog {α : Type} {enc : α ↪ List Bool} (L : Set α) (P : Prog)
    (budget K : α → ℕ) (c : ℕ)
    (logarithmic : ∀ a, (enc a).length.log2 + 1 ≤ budget a)
    (K_pos : ∀ a, 1 ≤ K a) (K_le : ∀ a, K a ≤ c * budget a)
    (bounded : ∀ a, P.Bounded (enc a) (2 ^ K a) [])
    (decides : ∀ a, (1 ≤ P.eval (enc a) [] ↔ a ∈ L)) :
    ∃ C, DecidableInTimeAndSpace L enc (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  set R := P.span + 1
  have hbudget (a : α) : 1 ≤ budget a := (Nat.le_add_left _ _).trans (logarithmic a)
  have hreg (a : α) {x : List ℕ} (hx : LeB (2 ^ K a) x) (hl : x.length = R) :
      (encList encNat x).length ≤ (R * (2 * c + 3)) * budget a := by
    refine (encList_le_of_LeB hx).trans ?_
    rw [hl, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith [K_le a, hbudget a])
  have run (a : α) := compile_correct (w := enc a) (B := 2 ^ K a)
    (by have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (K_pos a); simpa using this)
    P [] [] 0 1 (List.replicate R 0) ⟨rfl, fun i h => absurd h (by simp)⟩ (by omega)
    (by simp [R]; omega) (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact Nat.zero_le _)
        (bounded a)
  choose final hfinal using run
  refine Structured.decidable_of_exec L (P.compile [] 0 1) 0 R budget (R * (2 * c + 3))
    logarithmic final (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · obtain ⟨e, -⟩ := hfinal a
    exact (exec_weaken e fun x hx hl => hreg a hx (by simpa using hl)).1
  · obtain ⟨_, l, _, _, b⟩ := hfinal a
    exact hreg a b (by simpa using l)
  · obtain ⟨_, _, v, _, _⟩ := hfinal a
    rw [v]; exact decides a

end Decide

end Cslib.Complexity.NtimeDspace.ProgLang
