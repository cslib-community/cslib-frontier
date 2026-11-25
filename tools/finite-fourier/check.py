#!/usr/bin/env python3
"""Check the optional Fourier-to-Toeplitz implication using the pinned upstream statement.

From the built cslib-frontier checkout:

    python3 tools/finite-fourier/check.py /path/to/math/lean/ComparatorChallenges/ExactFourier.lean

Use openai/math commit 3344da59991ed94f9ba711217b29c1d760badfa6. The comparator contains
the published statement and admitted challenge commands. We import only the definitions
of its finite Fourier problem. The solution to that problem is proved separately by
OAI.LinearAlgebra.FiniteFourier.batchedFourierComplexity in the release's BatchedTheorem.lean.
This check proves the implication from its statement using frontier's pinned toolchain.
"""

import argparse
import hashlib
import os
import subprocess
import tempfile
from pathlib import Path


COMPARATOR_DIGEST = "5647dfdad6071be05e6445534ad417f88aec0c9cdbe2ec7dd029eabd708571d4"

# The comparator imports all of Mathlib, but the finite Fourier definitions use this subset.
IMPORTS = """import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.Exponent
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI
"""


def finite_fourier_definitions(comparator: Path) -> str:
    source = comparator.read_bytes()
    if hashlib.sha256(source).hexdigest() != COMPARATOR_DIGEST:
        raise SystemExit(f"{comparator} does not match the pinned ExactFourier.lean")
    text = source.decode("utf-8")
    start = text.index("namespace LinearAlgebra.FiniteFourier")
    end = text.index("/-- Theorem 1.1. The same positive lower constant")
    declarations = text[start:end].replace(
        "theorem fourierComplexity : FourierComplexityTheorem.{u,v} := by\n  sorry\n", ""
    )
    if "sorry" in declarations:
        raise SystemExit("unexpected admission in the extracted comparator definitions")
    return IMPORTS + declarations + "end LinearAlgebra.FiniteFourier\nend OAI\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("comparator", type=Path, help="the pinned ExactFourier.lean")
    definitions = finite_fourier_definitions(parser.parse_args().comparator)
    bridge = Path(__file__).resolve().with_name("ToeplitzFourier.lean")
    with tempfile.TemporaryDirectory(prefix="toeplitz-fourier-") as directory:
        source = Path(directory) / "PinnedFourier.lean"
        source.write_text(definitions, encoding="utf-8")
        subprocess.run(
            ["lake", "env", "lean", "-R", directory, "-o", source.with_suffix(".olean"), source],
            check=True,
        )
        paths = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], text=True).strip()
        subprocess.run(
            [
                "lake", "env", "env", f"LEAN_PATH={directory}{os.pathsep}{paths}", "lean",
                "-DautoImplicit=false", "-DwarningAsError=true", "-R", bridge.parent, bridge,
            ],
            check=True,
        )
    print("Checked the binary Toeplitz lower bound from the pinned batched Fourier theorem.")


if __name__ == "__main__":
    main()
