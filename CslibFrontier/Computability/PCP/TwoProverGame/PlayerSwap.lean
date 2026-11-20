/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Quantum
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Kronecker
import CslibFrontier.Probability.PMF.Map

/-!
# Exchanging the players in a tensor strategy

Exchange the question and answer alphabets, the local measurements and the two tensor
factors. The resulting answer law is the original law with the two outputs exchanged.
-/

public section

namespace Cslib.PCP

open Matrix Quantum
open scoped Kronecker

variable {X Y A B ι κ : Type*}

/-- Exchange the two players' questions, answers and positions in the verifier predicate. -/
@[expose] noncomputable def TwoProverGame.swap (G : TwoProverGame X Y A B) :
    TwoProverGame Y X B A where
  questions := G.questions.map Prod.swap
  accepts y x b a := G.accepts x y a b

namespace QuantumStrategy

variable [Fintype A] [Fintype B] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Exchange the two local measurements and permute the coordinates of the shared state. -/
@[expose] noncomputable def swap (S : QuantumStrategy X Y A B ι κ) :
    QuantumStrategy Y X B A κ ι where
  state := WithLp.toLp 2 (S.state.ofLp ∘ Prod.swap)
  norm_state := by
    rw [EuclideanSpace.norm_eq, ← S.norm_state, EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp (Equiv.prodComm κ ι) fun p => ‖S.state p‖ ^ 2
  alice := S.bob
  bob := S.alice

/-- The exchanged strategy returns the exchanged pair of answers with the same probability. -/
theorem answers_swap (S : QuantumStrategy X Y A B ι κ) (x : X) (y : Y) :
    S.swap.answers y x = (S.answers x y).map Prod.swap := by
  ext ⟨b, a⟩
  change S.swap.answers y x (b, a) = ((S.answers x y).map (Equiv.prodComm A B)) (b, a)
  rw [Cslib.Probability.PMF.map_equiv_apply]
  change S.swap.answers y x (b, a) = S.answers x y (a, b)
  rw [answers_apply, answers_apply]
  congr 2
  rw [← star_dotProduct_submatrix_mulVec (Equiv.prodComm ι κ)
    ((S.alice x).effect a ⊗ₖ (S.bob y).effect b) S.state.ofLp]
  rw [Equiv.prodComm_symm, submatrix_kronecker_prodComm]
  rfl

end QuantumStrategy

end Cslib.PCP
