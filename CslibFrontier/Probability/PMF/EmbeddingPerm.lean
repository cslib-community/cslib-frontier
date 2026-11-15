/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Init
public import Cslib.Probability.PMF
public import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Embedding

/-!
# Domain-permutation invariance of uniform embeddings

Precomposing a uniform embedding `T ↪ α` between finite types with a permutation `σ` of its domain
`T` leaves its distribution uniform (`uniformOfFintype_embedding_map_perm_trans`), so a uniform
embedding has the same law as a uniform embedding precomposed with an independent uniform
permutation of `T` (`uniformOfFintype_embedding_bind_perm_trans`).

## Main results

* `Cslib.Probability.PMF.uniformOfFintype_embedding_map_perm_trans`: precomposing a uniform
  embedding with a permutation of its domain leaves it uniform.
* `Cslib.Probability.PMF.uniformOfFintype_embedding_bind_perm_trans`: binding a uniform embedding
  is binding a uniform embedding precomposed with an independent uniform permutation of its domain.
-/

public section

namespace Cslib.Probability.PMF

universe u

/-- Precomposing a uniform embedding with a permutation of its domain leaves it uniform. -/
theorem uniformOfFintype_embedding_map_perm_trans {T α : Type u} [Fintype T] [Fintype α]
    [Nonempty (T ↪ α)] (σ : Equiv.Perm T) :
    (PMF.uniformOfFintype (T ↪ α)).map (fun j => σ.toEmbedding.trans j) =
      PMF.uniformOfFintype (T ↪ α) := by
  have h := PMF.uniformOfFintype_map_equiv (Equiv.embeddingCongr σ.symm (Equiv.refl α))
  convert h using 2
  ext j x
  simp

/-- Binding a uniform embedding `T ↪ α` is equivalent to binding a uniform embedding precomposed
with an independent uniform permutation of `T`. -/
theorem uniformOfFintype_embedding_bind_perm_trans {T α β : Type u} [Fintype T] [DecidableEq T]
    [Fintype α] [Nonempty (T ↪ α)] (f : (T ↪ α) → PMF β) :
    (PMF.uniformOfFintype (T ↪ α)).bind f =
      (PMF.uniformOfFintype (T ↪ α)).bind fun j =>
        (PMF.uniformOfFintype (Equiv.Perm T)).bind fun σ => f (σ.toEmbedding.trans j) := by
  rw [PMF.bind_comm]
  have key (σ : Equiv.Perm T) :
      (PMF.uniformOfFintype (T ↪ α)).bind (fun j => f (σ.toEmbedding.trans j)) =
        (PMF.uniformOfFintype (T ↪ α)).bind f := by
    conv_rhs => rw [← uniformOfFintype_embedding_map_perm_trans σ, PMF.bind_map]
    rfl
  simp_rw [key]
  rw [PMF.bind_const]

end Cslib.Probability.PMF
