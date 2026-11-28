# Commands and vocabulary

Run repository commands from its root. The [getting-started exercise](workflows/getting-started.md)
shows the complete first use; [contribution policy](../AGENTS.md#validation-sequence) governs
which evidence is required. A zero exit status means that command's stated scope passed.

| Situation | Command | Result and next step |
|---|---|---|
| Cold editor checkout | `scripts/cache/ensure.sh` | Attempts cache restoration; if imports are still missing, build the affected target or follow the cache guide |
| Check a complete named client | `scripts/build.sh CslibFrontierTests.NPCompleteness --wfail --iofail` | Builds that client and dependencies; inspect the first error before broadening the build |
| Check library changes and importing clients | `scripts/check.sh --quick --no-full-fallback` | Checks manuals, changed sources and transitive importing clients; inspect the reported scope. Status 3 means quick mode cannot plan the change: run focused checks and use hosted CI for full validation |
| Full local validation when explicitly requested or hosted CI is unavailable | `scripts/check.sh` | Runs the manuals and every locally runnable required CI step, including the six Lean gates; any failure prevents treating the run as full validation. Successful CI covering the final revision need not be repeated locally |
| Add a library module | `lake exe mk_all` | Regenerates the library aggregate; inspect its diff and check the affected client |
| Check aggregate completeness | `lake exe mk_all --check` | Fails if an aggregate is stale; regenerate it and review the change |
| Check manual links and contextual excerpts | `python3 scripts/check_operator_manual.py` | Reports current-source matches, broken links, source line links that no longer start a declaration or that miss the declaration of the linked file their link text names, list items directly after a paragraph line (which the PDF prints as running text), locators such as `Section 5.6` inside the label of a link into `sources.md` (which the PDF replaces by a citation number), lines of `sources.md` with more than one sentence, and pages missing from the book's chapter lists; repair the affected prose, link, canonical example or list |
| Format the manual bibliography one sentence per line | `python3 scripts/sources_format.py --write` | Splits multi-sentence lines of `manual/sources.md` while keeping every word and block unchanged |
| Repoint drifted declaration line anchors in manuals | `python3 scripts/check_operator_manual.py --fix-anchors` | Updates drifted `[Ns.name](File.lean#Ln)` links whose named declaration has a unique current header before running the link check; inspect remaining ambiguous, range or prose anchor errors by hand |
| Check the manual checker | `python3 scripts/test_operator_manual.py` | Runs isolated positive and negative controls; failure identifies a checker regression |
| Generate an editable book | `python3 scripts/build_operator_manual.py` | Writes LaTeX/PDF under ignored `manual/_build/`; inspect changed pages before distributing |
| See isolated worktrees | `scripts/worktree.sh list` | Lists registered work; inspect ownership before takeover or removal |
| Queue an approved PR | `python3 <trusted-helper> <PR> <approved head> --repo OWNER/NAME` | Use the [helper from current main](workflows/agent-operations.md#queue-approved-work-and-keep-its-approval); queues exactly the approved head after review holds clear and required checks pass |
| Find approved PRs that are not queued | `python3 scripts/tender_report.py` | Read-only. Lists PRs approved at their exact head with green checks and no live hold, those needing a human read of a hold, restack candidates, expired `HOLD` lines, expired review claims and released PRs not yet taken over; [read the PR](workflows/agent-operations.md#find-ready-stalled-and-finished-work) before queueing |
| Find stalled drafts, claims and change requests | `python3 scripts/stale_notices.py` | Dry run lists drafts idle 7 days, issue claims idle 3 days and change requests unanswered 48 hours. `--apply --identity <text>` posts one marked notice per stall (skipping items already noticed since their last activity or within 24 hours); it never closes anything |
| Find branches that can be deleted | `python3 scripts/branch_cleanup.py --delete merged` | Dry run categorizes every branch and lists unprotected ones of the selected kinds (`merged`, `closed`, `nopr`; the last two need `--older-than`, default 14d). `--apply` deletes them, writes a JSON log and prints a restore command per branch. No-PR branches need a notice first: `--notice --identity <text>` writes comment file(s) (`--notice-report` prints the table), and `--delete nopr --apply` needs `--notice-issue <N>` |
| Remove a PR from the merge queue before pushing to it | `gh api graphql -f id="$(gh pr view <PR> --json id --jq .id)" -f query='mutation($id: ID!) { dequeuePullRequest(input: {id: $id}) { mergeQueueEntry { state } } }'` | GitHub declines pushes to a queued PR's branch; this (or **Remove from queue** on the PR page) removes it and merges nothing. Push the restack, then queue the new head under [Restacks](../AGENTS.md#restacks) |
| Check a restacked PR | `python3 scripts/check_restack.py <approved head> <new head>` | Run from a checkout of current `origin/main`. For a PR approved while stacked, add `--approved-base <lower head at approval>`. Exit 0: the new head is the approved change replayed onto newer `main`, and the approval carries once CI passes at the new head; exit 1: review the printed diffs |
| Restack a PR whose only conflicts are in generated files, `references.bib` or `manual/sources.md` | `python3 scripts/restack_mechanical.py <PR> --approved-head <approved head>` | Dry run: refuses a head that is not the approved change, merges `origin/main` with the aggregate, bibliography and sources drivers, writes the aggregates as `mk_all` would and runs the restack check; refuses any other conflict. Add `--push` to publish the merge, which happens only if the check passes and the branch has not moved; once CI passes and review holds clear, use the printed PR/head with the [trusted queue helper](workflows/agent-operations.md#queue-approved-work-and-keep-its-approval) |

The full validation sequence is maintained in [AGENTS.md](../AGENTS.md#validation-sequence),
and cache behavior in [the cache guide](../scripts/cache/README.md). Commands above call
those same scripts; they do not define an independent validation policy.

## Search before adding an API

The following read-only searches use `rg` (ripgrep). If it is unavailable, use editor
workspace search. After dependencies are present, search all three libraries:

```bash
rg -n 'ComputableInPolyTime' CslibFrontier CslibFrontierTests .lake/packages/cslib/Cslib
rg -n 'iterate_spec|iterateWith_spec' CslibFrontier .lake/packages/cslib/Cslib
rg -n 'yourCandidateName' CslibFrontier .lake/packages/cslib/Cslib .lake/packages/mathlib/Mathlib
```

A hit gives a source location to inspect, not an interchangeable theorem. Read its full
statement and imports. If there are no hits, check spelling and namespace, related notions,
the [model routes](workflows/finding-results.md) and [upstream coordination](../CONTRIBUTING.md#upstreaming)
before declaring the API absent.

## Vocabulary

| Term | Meaning in the manual |
|---|---|
| Model | A specified syntax or state space, semantics and resource convention |
| Encoding | The representation of an input or output as a finite word; its length affects bounds |
| Plain computability | The public machine-existence/resource contract; tidy machine machinery stays inside proofs |
| Certificate | A Lean proof of a stated property, such as computation cost; it does not supply unrelated functional correctness |
| Program | Free syntax that can be interpreted with semantics and resource bounds; a PMF alone describes a distribution |
| Native realization | A theorem connecting a program or abstract model to the selected machine interface |
| Uniformity | A single effective construction or machine across inputs/sizes; separate per-size existence is weaker |
| Bridge | A proved translation between specified models, preserving the advertised semantics and charging its overhead |
| Contextual excerpt | Exact code from a linked complete client; imports, namespaces and preceding assumptions remain necessary |
| Validation | The checks actually run on a stated revision, with their scope and outcome |
| Independent review | Inspection by a non-author who did not design or implement the reviewed change |
| Snapshot evidence | A dated source or development observation; it does not automatically describe later revisions |

For the model-specific meaning of time, workspace, error, query cost, circuit size, advice,
adversary access and other resources, use the [model selection table](workflows/choosing-models.md)
and its linked reference chapters. Do not infer one resource convention from another's name.
