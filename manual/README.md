# cslib-frontier Operator's Manual

This is the substantial manual for humans or agents using, changing and reviewing the
cslib-frontier codebase. It explains models, tactics, proof interfaces, design and development
procedures. It assumes basic Lean literacy; a human should be able to follow the workflows
with a text editor, Git, Python and Lake. AI tools are optional.

The separate [Agent Operator's Manual](AGENT_OPERATORS.md) is a short guide for the human
driving agents: choosing roles, assigning work, requesting review, handing off and intervening.
Use that manual to direct a session, and this manual for the codebase operations performed
within it.

Start with [getting a checkout and checking a complete client](workflows/getting-started.md).
The [first contribution exercise](workflows/getting-started.md#a-first-worked-example)
leads from an isolated branch through a successful check, an expected failure, its repair,
and a reviewable handoff. [Choose a model](workflows/choosing-models.md) before stating a
resource bound: the encoding and cost convention are part of the theorem.

| Task | Route |
|---|---|
| Build, inspect and change a first client | [Get started](workflows/getting-started.md) |
| Use the library in another Lean project | [Add a pinned dependency](workflows/getting-started.md#use-cslib-frontier-from-your-own-project) |
| State a model and resource contract | [Choose a model](workflows/choosing-models.md) |
| Compose deterministic certificates or prove P/NP membership | [Deterministic workflows](workflows/deterministic-workflows.md) |
| Write randomized or oracle programs and prove efficiency | [Probabilistic workflows](workflows/probabilistic-workflows.md) |
| Locate a theorem and check its assumptions | [Find results](workflows/finding-results.md) |
| Understand a failed proof or build | [Troubleshoot](workflows/troubleshooting.md) |
| Prepare, validate and review a change | [Contribute and review](workflows/contributing.md) |
| Look up a command or term | [Commands and vocabulary](COMMANDS.md) |
| Coordinate implementation and review | [Participant and reviewer procedures](workflows/agent-operations.md) |
| Direct agents as their human operator | [Agent Operator's Manual](AGENT_OPERATORS.md) |

## Library map

The [reference chapters](index.md) and [model map](model-map.md) are frozen snapshots from
November 2026. For current declarations, search the [API reference](https://www.cslib.io/cslib-frontier/search.html)
or open the [Lean source](../CslibFrontier/). The [results inventory](../results/README.md) lists
selected theorems and their sources. The [guide](https://www.cslib.io/cslib-frontier/guide/) walks
through checked examples, and the [codebase views](https://www.cslib.io/cslib-frontier/viz/) show
how the modules depend on each other and how the library has grown.

| Source directory | Chapters and examples |
| --- | --- |
| `Computability/` | [Machines and complexity classes](machines-and-classes/index.md) and [circuits](circuits-logic-and-other-models/index.md). Examples cover [polynomial time](../CslibFrontierTests/PolyTimeTactic.lean), [time classes](../CslibFrontierTests/TimeClasses.lean), [NP-completeness](../CslibFrontierTests/NPCompleteness.lean) and [uniform circuits](../CslibFrontierTests/UniformCircuits.lean). |
| `Algorithms/` | [Algorithms, memory and data structures](algorithms-and-memory/index.md), including a [worked Dijkstra example](../CslibFrontierTests/Dijkstra.lean). |
| `DataStructure/` | [Dictionaries and hashing](algorithms-and-memory/dictionaries-hashing-and-randomized.md), the [Count-Min sketch](../CslibFrontierTests/CountMin.lean) and its [accuracy bound](../CslibFrontier/DataStructure/CountMin/Probability.lean). |
| `Crypto/` | [Cryptography](programs-crypto-and-probability/index.md), with examples of [probabilistic polynomial-time programs](../CslibFrontierTests/PPTTactic.lean) and [oracle reductions](../CslibFrontierTests/OraclePPT.lean). |
| `Languages/`, `Probability/` | [Probabilistic programs and their semantics](programs-crypto-and-probability/programs-and-realization.md). The [SQL semantics](circuits-logic-and-other-models/sql-semantics.md) has [join-size examples](../CslibFrontierTests/Languages/SQL/JoinSize.lean). |
| `Privacy/` | [Differential privacy](programs-crypto-and-probability/protocols-and-privacy.md). |
| `Logics/` | [Proof complexity](circuits-logic-and-other-models/proof-systems.md) and [finite-model logic](circuits-logic-and-other-models/finite-model-logic.md), with [fixed-point and transitive-closure examples](../CslibFrontierTests/FOOperators.lean) and [Immerman–Vardi](../CslibFrontier/Computability/Complexity/ImmermanVardi.lean). |
| `MachineLearning/` | [Learning and property testing](circuits-logic-and-other-models/learning-and-testing.md). |
| `GameTheory/` | [Strategic games](algorithms-and-memory/strategic-games.md) and [mechanism design](algorithms-and-memory/mechanism-design.md). |
| `Tactic/` | [Proof automation](design-and-assurance/automation.md). |
| `Foundations/` | [General mathematics](../CslibFrontier/Foundations/) used by the other areas, including combinatorics, Boolean analysis and number theory. |

The deterministic polynomial-time examples build on Christian Reitwiessner's tidy machine
calculus. The [Clique proof](../CslibFrontier/Computability/Complexity/Problems/Clique.lean)
uses graph complementation to reduce Independent Set to Clique. The
[reduction index](../CslibFrontier/Computability/Complexity/Reduction.lean) points to more
NP-completeness proofs.

## Maintain the procedure pages and registries

Under the [contribution policy](../CONTRIBUTING.md#maintaining-the-manuals), a change to a
procedure or role updates the page that describes it, and a change to a fact recorded in a
registry updates the registry. Nothing else in a PR requires a manual edit. Read the
[maintenance procedure](MAINTAINING.md) for what to inspect and how to validate it.

```bash
python3 scripts/check_operator_manual.py
python3 scripts/test_operator_manual.py
```

Run these commands from the repository root. The first checks local links, visual markup, the
book's chapter lists and the identity of contextual Lean excerpts against the current source
(in frozen chapters, only their own markup and the links between them);
the second exercises failure cases of that checker. Neither compiles Lean or establishes that
the prose describes the right mathematics. Check affected complete clients through Lake as the
workflows describe.

## Read or build the manuals

Markdown is canonical and readable directly in the checkout. To generate the editable
LaTeX source and PDF for each manual:

```bash
python3 scripts/build_operator_manual.py
python3 scripts/build_operator_manual.py --agent-manual
```

The [build instructions](BUILD.md) list optional publishing tools and output locations.
Book products live under ignored `manual/_build/`; optional research exports use
`manual/_generated/`. Neither is maintained by hand.

## History

The [History](history/index.md) part keeps the dated record from the complexitylib period: the
2 November 2026 source survey from which the reference chapters grew, and the study of the
library's automated development. Its measurements stay fixed to their stated revision; they
explain earlier decisions but do not describe the current library.
