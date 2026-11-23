/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.RelationAlgebra.AtomTable
public import Mathlib.Computability.RE
import CslibFrontier.Computability.RelationAlgebra.Tiling.Reduction
import CslibFrontier.Computability.WangTile.TilesPlaneOfEveryTileOccurs
import CslibFrontier.Computability.WangTile.Undecidable

/-!
# Undecidability of representability for finite relation algebras

No algorithm decides whether a finite relation algebra is representable [HirschHodkinson2001],
Theorem 8. The instances here are atom tables: every finite relation algebra is isomorphic to the
complex algebra of an atom structure that some table presents
(`Cslib.RelationAlgebra.AtomTable.exists_presents_equiv`), and isomorphic relation algebras are
both representable or both not (`Cslib.RelationAlgebraEquiv.representable_iff`; for finite ones in
different universes, by `Cslib.RelationAlgebra.Representation.representable`). A table that
presents no atom structure, or one violating the laws of an atom structure (so that its complex
algebra is not a relation algebra), is a no-instance. `Representable` is cslib's: an injective
homomorphism into a product of algebras of all relations on a set. Its relation to the source's
representations, which have non-empty domains, is described in the module
`CslibFrontier.Foundations.RelationAlgebra.Game`.

A decision procedure for the representation problem decides the tiling problem in which every
tile must occur, through the reduction
`Cslib.RelationAlgebra.everyTileOccurs_manyOneReducible_isRepresentable`. That gives a decision
procedure for the domino problem by a search over sublists
(`Cslib.WangTile.computablePred_tilesPlane_of_computablePred_everyTileOccurs`), and the domino
problem is undecidable (`Cslib.WangTile.not_computablePred_tilesPlane`, Berger's theorem). The
source cites Berger's theorem and says without argument that its tiling problem is undecidable
too; the search over sublists is our argument for that step.

## Main results

* `Cslib.RelationAlgebra.AtomTable.not_computablePred_representable_complexAlgebra`: the
  representation problem for finite relation algebras given by tables is undecidable.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

public section

namespace Cslib.RelationAlgebra.AtomTable

open WangTile

/-- **Representability of finite relation algebras is undecidable** [HirschHodkinson2001],
Theorem 8: no algorithm decides whether a table presents a lawful atom structure whose complex
algebra is representable. The predicate is `AtomTable.IsRepresentable`, written out. -/
theorem not_computablePred_representable_complexAlgebra :
    ¬ComputablePred fun t : AtomTable =>
      ∃ A : AtomStructure (Fin t.size), t.Presents A ∧
        ∃ _ : LawfulAtomStructure A, Representable (ComplexAlgebra A) :=
  fun hrep =>
    not_computablePred_tilesPlane <|
      computablePred_tilesPlane_of_computablePred_everyTileOccurs <|
        ComputablePred.computable_of_manyOneReducible
          everyTileOccurs_manyOneReducible_isRepresentable hrep

end Cslib.RelationAlgebra.AtomTable
