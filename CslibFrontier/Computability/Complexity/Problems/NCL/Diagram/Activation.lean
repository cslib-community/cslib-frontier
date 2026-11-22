/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Glue
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word
public import CslibFrontier.Computability.Complexity.Problems.NCL.Simulation

/-!
# Activating forward circuits in creation order

A vertex is forward when its positive ports precede its negative ports in an edge numbering.
Between two legal orientations `s ≤ t`, replacing the bits of `s` by those of `t` in that order
keeps every vertex legal. Before its outputs change, the vertex has at least its initial inflow;
once its outputs change, its inputs already have their final values.

This original argument turns static evaluations of acyclic circuits into execution paths.
It applies to diagrams whose generators read top wires positively and bottom wires negatively.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.Interp.Forward`: generators use the forward port convention.
* `Cslib.Complexity.NCL.Diagram.off`: keep the incoming bits and clear all created wires.

## Main results

* `Cslib.Complexity.NCL.Diagram.reachable_of_le_within`: an invariant holding throughout the
  Boolean interval also holds throughout the activation path.
* `Cslib.Complexity.NCL.Diagram.innerReach_of_le`: the path keeps every unchanged boundary.
* `Cslib.Complexity.NCL.Diagram.legal_off`: clearing created wires gives a legal starting point
  when the all-false orientation is legal.
* `Cslib.Complexity.NCL.Diagram.legal_top_mono`: increasing only incoming directions preserves
  legality.

## References

* The CNF circuit application follows [Hearn and Demaine][HearnDemaine2005, Lemma 2].
-/

public section

namespace Cslib.Complexity.NCL

variable {E : Type*}

/-- A vertex whose positive ports precede its negative ports in the given numbering. -/
private def Vertex.Forward (v : Vertex E) (rank : E → ℕ) : Prop :=
  ∃ k, ∀ p ∈ v.ports, (p.port.dir = true → rank p.port.edge < k) ∧
    (p.port.dir = false → k ≤ rank p.port.edge)

@[simp] private theorem Vertex.forward_map {E' : Type*} (f : E → E') (v : Vertex E)
    (rank : E' → ℕ) :
    (v.map f).Forward rank ↔ v.Forward (rank ∘ f) := by
  simp only [Forward, Vertex.map, List.forall_mem_map, WeightedPort.map,
    Port.map, Function.comp_def]

private def sweep (rank : E → ℕ) (s t : E → Bool) (k : ℕ) (e : E) : Bool :=
  if rank e < k then t e else s e

private theorem sat_sweep {v : Vertex E} {rank : E → ℕ} (hv : v.Forward rank)
    {s t : E → Bool} (hs : v.Sat s) (ht : v.Sat t) (hle : ∀ e, s e ≤ t e) (n : ℕ) :
    v.Sat (sweep rank s t n) := by
  obtain ⟨k, hk⟩ := hv
  by_cases hn : n ≤ k
  · apply hs.mono
    intro p hp hin
    cases hd : p.port.dir with
    | false =>
      have hr : ¬rank p.port.edge < n := by have := (hk p hp).2 hd; omega
      simpa only [Port.In, sweep, ite_eq_right hr] using hin
    | true =>
      by_cases hr : rank p.port.edge < n
      · exact (ite_eq_left hr).trans (Bool.le_iff_imp.1 (hle _)
          (by simpa only [Port.In, hd] using hin)) |>.trans hd.symm
      · simpa only [Port.In, sweep, ite_eq_right hr] using hin
  · apply ht.mono
    intro p hp hin
    cases hd : p.port.dir with
    | true =>
      have hr : rank p.port.edge < n := by have := (hk p hp).1 hd; omega
      simpa only [Port.In, sweep, ite_eq_left hr] using hin
    | false =>
      by_cases hr : rank p.port.edge < n
      · simpa only [Port.In, sweep, ite_eq_left hr] using hin
      · have he : s p.port.edge = false := Bool.eq_false_of_not_eq_true fun h =>
          Bool.noConfusion ((Bool.le_iff_imp.1 (hle _) h).symm.trans
            (by simpa only [Port.In, hd] using hin))
        simpa only [Port.In, sweep, ite_eq_right hr, hd] using he

private theorem sweep_reverse [DecidableEq E] {rank : E → ℕ} (hrank : Function.Injective rank)
    (s t : E → Bool) (n : ℕ) (e : E) (he : rank e = n) (hne : s e ≠ t e) :
    sweep rank s t (n + 1) = reverse (sweep rank s t n) e := by
  funext f
  by_cases hf : f = e
  · subst f
    simp only [sweep, he, Nat.lt_succ_self, Nat.lt_irrefl, ite_true, ite_false, reverse_self]
    cases hs : s e <;> cases ht : t e <;> simp_all
  · have hn : rank f ≠ n := fun h => hf (hrank (h.trans he.symm))
    rw [reverse_of_ne _ hf]
    have hlt : rank f < n + 1 ↔ rank f < n := by omega
    simp only [sweep, hlt]

private theorem sweep_path {rank : E → ℕ} (s t : E → Bool) {r : (E → Bool) → (E → Bool) → Prop}
    (hstep : ∀ n e, rank e = n → s e ≠ t e → r (sweep rank s t n) (sweep rank s t (n + 1))) :
    ∀ n, Relation.ReflTransGen r s (sweep rank s t n)
  | 0 => by
    rw [show sweep rank s t 0 = s from funext fun e => by simp [sweep]]
  | n + 1 => by
    classical
    by_cases h : ∃ e, rank e = n ∧ s e ≠ t e
    · obtain ⟨e, he, hne⟩ := h
      exact (sweep_path s t hstep n).tail (hstep n e he hne)
    · have heq : sweep rank s t (n + 1) = sweep rank s t n := by
        funext e
        by_cases he : rank e = n
        · have hst : s e = t e := not_not.1 fun hne => h ⟨e, he, hne⟩
          simp [sweep, he, hst]
        · have hlt : rank e < n + 1 ↔ rank e < n := by omega
          simp only [sweep, hlt]
      rw [heq]
      exact sweep_path s t hstep n

namespace Diagram

variable {Γ : List Color → List Color → Type} {I : Interp Γ} {a b c d : List Color}

/-- Every generator reads its top ports positively and its bottom ports negatively. -/
@[expose] def Interp.Forward (I : Interp Γ) : Prop :=
  ∀ {a b} (g : Γ a b) (v : Vertex (Fin a.length ⊕ Fin b.length)), v ∈ I.verts g →
    ∀ p ∈ v.ports, p.port.dir = Sum.elim (fun _ => true) (fun _ => false) p.port.edge

/-- Increasing only the incoming directions preserves legality in a forward diagram. -/
theorem legal_top_mono (hI : I.Forward) (D : Diagram Γ a b) {s t : D.Edge → Bool}
    (hs : (D.graph I).Legal s) (htop : ∀ i, s (.inl i) ≤ t (.inl i))
    (hinner : ∀ e, s (.inr e) = t (.inr e)) : (D.graph I).Legal t := by
  have hle : ∀ e, s e ≤ t e := fun e => by
    cases e with
    | inl i => exact htop i
    | inr e => exact (hinner e).le
  induction D with
  | gen g =>
    intro v
    refine Vertex.Sat.mono (fun p hp hin => ?_) (hs v)
    have hd := hI g _ (List.get_mem _ v) p hp
    change s p.port.edge = p.port.dir at hin
    rcases he : p.port.edge with i | e
    · have hdir : p.port.dir = true := by rw [he] at hd; exact hd
      change t p.port.edge = p.port.dir
      rw [he, hdir]
      have hsin : s (.inl i) = true := by simpa only [he, hdir] using hin
      exact Bool.eq_true_of_true_le (by simpa only [hsin] using htop i)
    · change t p.port.edge = p.port.dir
      rw [he, ← hinner e]
      simpa only [he] using hin
  | id a => exact fun v => v.elim
  | swap x y => exact fun v => v.elim
  | comp D₁ D₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := (legal_comp_iff D₁ D₂ s).1 hs
    exact (legal_comp_iff D₁ D₂ t).2
      ⟨ih₁ h₁ (fun i => htop i) (fun e => hinner (.inl e))
        (fun e => hle (compLeft D₁ D₂ e)),
       ih₂ h₂ (fun i => hle (compRight D₁ D₂ (.inl i))) (fun e => hinner (.inr e))
        (fun e => hle (compRight D₁ D₂ e))⟩
  | tensor D₁ D₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := (legal_tensor_iff D₁ D₂ s).1 hs
    exact (legal_tensor_iff D₁ D₂ t).2
      ⟨ih₁ h₁ (fun i => hle (tensorLeft D₁ D₂ (.inl i))) (fun e => hinner (.inl e))
        (fun e => hle (tensorLeft D₁ D₂ e)),
       ih₂ h₂ (fun i => hle (tensorRight D₁ D₂ (.inl i))) (fun e => hinner (.inr e))
        (fun e => hle (tensorRight D₁ D₂ e))⟩

private theorem forward_gen (hI : I.Forward) {a b : List Color} (g : Γ a b)
    (top : Fin a.length → ℕ) (k : ℕ) (htop : ∀ i, top i < k) (v : Vertex _) (hv : v ∈ I.verts g) :
    v.Forward ((gen g).name top k) := by
  refine ⟨k, fun p hp => ?_⟩
  have hd := hI g v hv p hp
  rcases he : p.port.edge with i | j
  · have hd' : p.port.dir = true := by simpa only [he, Sum.elim_inl] using hd
    refine ⟨fun _ => ?_, fun h => Bool.noConfusion (hd'.symm.trans h)⟩
    simpa only [name, Inner, he, Sum.elim_inl] using htop i
  · have hd' : p.port.dir = false := by simpa only [he, Sum.elim_inr] using hd
    refine ⟨fun h => Bool.noConfusion (hd'.symm.trans h), fun _ => ?_⟩
    simpa only [name, Inner, he, Sum.elim_inr, idx] using Nat.le_add_right k (j : ℕ)

private theorem forward_vertexList (hI : I.Forward) (D : Diagram Γ a b)
    (top : Fin a.length → ℕ) (k : ℕ) (htop : ∀ i, top i < k) :
    ∀ v ∈ vertexList I D, v.Forward (D.name top k) := by
  induction D generalizing k with
  | gen g => exact forward_gen hI g top k htop
  | id a => simp [vertexList]
  | swap x y => simp [vertexList]
  | comp D₁ D₂ ih₁ ih₂ =>
    simp only [vertexList, List.forall_mem_append, List.forall_mem_map, Vertex.forward_map]
    constructor
    · simpa only [Function.comp_def, name_compLeft] using ih₁ top k htop
    · simpa only [Function.comp_def, name_compRight] using
        ih₂ (fun j => D₁.name top k (D₁.bottom j)) (k + D₁.innerCount)
          (fun j => name_lt D₁ top k htop (D₁.bottom j))
  | @tensor a b c d D₁ D₂ ih₁ ih₂ =>
    simp only [vertexList, List.forall_mem_append, List.forall_mem_map, Vertex.forward_map]
    constructor
    · simpa only [Function.comp_def, name_tensorLeft] using
        ih₁ (fun i => top ((List.appendIndexEquiv a c) (.inl i))) k (fun i => htop _)
    · simpa only [Function.comp_def, name_tensorRight] using
        ih₂ (fun i => top ((List.appendIndexEquiv a c) (.inr i))) (k + D₁.innerCount)
          (fun i => (htop _).trans_le (Nat.le_add_right _ _))

private theorem legal_sweep (hI : I.Forward) (D : Diagram Γ a b) {s t : D.Edge → Bool}
    (hs : (D.graph I).Legal s) (ht : (D.graph I).Legal t) (hle : ∀ e, s e ≤ t e) (n : ℕ) :
    (D.graph I).Legal (sweep D.num s t n) := by
  apply (forall_vertexList_iff D _).1
  intro v hv
  exact sat_sweep (forward_vertexList hI D Fin.val a.length (fun i => i.isLt) v hv)
    ((forall_vertexList_iff D _).2 hs v hv) ((forall_vertexList_iff D _).2 ht v hv) hle n

/-- Increasing legal orientations are connected inside any invariant that holds on their
Boolean interval. The path scans the edges in creation order. -/
theorem reachable_of_le_within (hI : I.Forward) (D : Diagram Γ a b) {s t : D.Edge → Bool}
    (hs : (D.graph I).Legal s) (ht : (D.graph I).Legal t) (hle : ∀ e, s e ≤ t e)
    {P : (D.Edge → Bool) → Prop}
    (hP : ∀ u, (∀ e, s e ≤ u e) → (∀ e, u e ≤ t e) → P u) :
    Relation.ReflTransGen (Within (D.graph I).Step P) s t := by
  have hp (n : ℕ) : P (sweep D.num s t n) := by
    apply hP
    · intro e
      dsimp only [sweep]
      split <;> first | exact hle e | exact le_rfl
    · intro e
      dsimp only [sweep]
      split <;> first | exact hle e | exact le_rfl
  have h := sweep_path s t (rank := D.num) (r := Within (D.graph I).Step P) fun n e he hne =>
    ⟨hp n, legal_sweep hI D hs ht hle n, legal_sweep hI D hs ht hle (n + 1), e,
      sweep_reverse D.num_injective s t n e he hne⟩
  have hfinal : sweep D.num s t (a.length + D.innerCount) = t :=
    funext fun e => ite_eq_left (D.num_lt e)
  exact hfinal ▸ h _

/-- When the boundaries agree, creation-order activation moves only internal edges. -/
theorem innerReach_of_le (hI : I.Forward) (D : Diagram Γ a b) {s t : D.Edge → Bool}
    (hs : (D.graph I).Legal s) (ht : (D.graph I).Legal t) (hle : ∀ e, s e ≤ t e)
    (hboundary : ∀ e, D.IsBoundary e → s e = t e) : InnerReach I D s t := by
  have h := sweep_path s t (rank := D.num) (r := InnerStep I D) fun n e he hne =>
    ⟨legal_sweep hI D hs ht hle n, legal_sweep hI D hs ht hle (n + 1), e,
      fun hb => hne (hboundary e hb), sweep_reverse D.num_injective s t n e he hne⟩
  have hfinal : sweep D.num s t (a.length + D.innerCount) = t :=
    funext fun e => ite_eq_left (D.num_lt e)
  exact hfinal ▸ h _

/-- Keep the top directions of an orientation and clear every wire created inside the diagram. -/
@[expose] def off (D : Diagram Γ a b) (t : D.Edge → Bool) : D.Edge → Bool :=
  Sum.elim (fun i => t (.inl i)) (fun _ => false)

@[simp] theorem off_false (D : Diagram Γ a b) : D.off (fun _ => false) = (fun _ => false) := by
  funext e
  cases e <;> rfl

@[simp] theorem off_id (a : List Color) (t : (Diagram.id a : Diagram Γ a a).Edge → Bool) :
    (Diagram.id a).off t = t := by
  funext e
  rcases e with i | e
  · rfl
  · exact e.elim

@[simp] theorem off_glueComp (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (s : D₁.Edge → Bool) (t : D₂.Edge → Bool) :
    (D₁.comp D₂).off (glueComp D₁ D₂ s t) =
      glueComp D₁ D₂ (D₁.off s) (D₂.off t) := by
  funext e
  rcases e with i | e | e <;> rfl

@[simp] theorem off_glueTensor (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (s : D₁.Edge → Bool) (t : D₂.Edge → Bool) :
    (D₁.tensor D₂).off (glueTensor D₁ D₂ s t) =
      glueTensor D₁ D₂ (D₁.off s) (D₂.off t) := by
  funext e
  rcases e with i | e | e
  · simp only [off, glueTensor, Sum.elim_inl]
  · rfl
  · rfl

/-- The inactive version of a legal orientation is legal when all-false is legal. -/
theorem legal_off (hI : I.Forward) (D : Diagram Γ a b)
    (hzero : (D.graph I).Legal (fun _ => false)) {t : D.Edge → Bool}
    (ht : (D.graph I).Legal t) : (D.graph I).Legal (D.off t) := by
  have heq : sweep D.num (fun _ => false) t a.length = D.off t := by
    funext e
    rcases e with i | e
    · exact ite_eq_left i.isLt
    · exact ite_eq_right (by simp [num, name])
  exact heq ▸ legal_sweep hI D hzero ht (fun _ => Bool.false_le _) a.length

end Diagram

end Cslib.Complexity.NCL
