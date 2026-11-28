# Coordinate implementation and review

This chapter is the codebase coordination reference for participants and reviewers, whether
human or agent. It covers task ownership, isolated work, validation evidence and review handoffs.
The human directing agents should start with the separate
[Agent Operator's Manual](../AGENT_OPERATORS.md) for assignment and intervention procedures.
A short Lean proof can certify an unintended statement; a merged milestone can leave the
original objective unresolved. The [development study](../history/development.md)
supplies historical evidence separately. [cslib-frontier][complexitylib]

## Specify a bounded task and a visible endpoint

Before implementation, record the intended theorem or API, model, encoding, allowed hypotheses,
resource bound, existing source, representative client and owned files. Record the active
contributor or agent/session and branch in the issue or PR; a shared GitHub account does not
distinguish agents. Resolve an unclear contract with the task owner before extending its scope.

A task brief might request a named problem's membership in `NP` under a specified encoding, with a verifier and certificate-length bound. Say whether a reduction or completeness theorem is also required. That keeps a membership proof from silently becoming a report that completeness is done.

Choose parallel tasks with separate mutable files and build outputs. Prioritize fixes and landing existing work when review or integration is the bottleneck. Before taking over work, inspect its issue, PR and activity and notify its owner in the task record. A claim with no open PR and no activity is released 24 hours after that notice, or 6 hours when its owner is an agent session on the same GitHub account; a PR awaiting review is never released by silence, and one whose author has not answered a request for changes for 48 hours is converted to draft. A stacked chain has at most three open unlanded layers ([Stacked chains](../../policy/review.md#stacked-chains)). Follow the [role and ownership rules](../../AGENTS.md#agent-roles-and-task-ownership).

## Isolate work and build outputs

For a new branch based on the primary checkout’s current commit:

```bash
scripts/worktree.sh create feat/manual-example manual-example HEAD
```

The helper creates the worktree under `.worktrees/` and prepares caches. It resolves the shared repository’s primary root before interpreting `HEAD`; pass an explicit commit SHA to branch from another worktree’s revision. Choose a fresh task-specific branch and directory. Existing local and remote branches have different handling; read the helper's usage before takeover. Do not use reset options just to obtain a clean start.

Package sources may be hard-linked by default, while mutable build outputs are copied independently. Do not edit shared package sources. Use `--copy-cslib` or `--copy-packages` when dependencies must change. `--source-only` avoids initial `.lake` seeding when existing pins or artifacts are unsuitable. The [cache/isolation guide](../../scripts/cache/README.md#automatic-restoration) explains these modes.

Coordinate a thread budget on shared machines. `LEAN_NUM_THREADS=2 scripts/check.sh` is an example setting, not a hard process or memory limit: during the cache-restore audit, `scripts/check.sh` launches up to 8 concurrent `lean` processes unless capped by `LEAN_NUM_THREADS` or `CSLIB_FRONTIER_CACHE_AUDIT_JOBS`. On a busy host, the kernel's file-handle table can be exhausted first, so also bound the number of concurrent Lean builds; see [Diagnose "Too many open files in system"](troubleshooting.md#diagnose-too-many-open-files-in-system). Stop only tasks you started, by recorded PID or task ID. Preserve completed artifacts when rescheduling. Ordinary worktrees share a Git object database; history-repair experiments require an independent repository.

Worktrees also share one stash stack, `refs/stash`, so `git stash pop` in your worktree can apply and drop an entry that another session pushed from its own. Do not push, pop, apply or drop stash entries in a shared checkout or its worktrees. To set work aside, stage it with `git add -A`, then either commit it on your own branch (`git reset --soft HEAD~` undoes the commit later) or save `git diff --cached --binary` to a file under your scratch directory, check that the file is non-empty, and clear the work with `git reset --hard`; `git apply --index` restores it. If a pop completed and applied another session's entry, its last line names the dropped commit. Put the entry back with `git stash store -m "$(git log -1 --format=%s <commit>)" <commit>`, restore the files it changed in your worktree, and tell the entry's owner. A pop that stops on a conflict keeps the entry on the stack; restore your files and leave the entry alone.

## Separate implementation and review

Inspect existing definitions before introducing abstractions. Require the exact Lean contract and source-to-statement mapping for a claimed textbook endpoint. During implementation use focused diagnostics and clients; at handoff use the [contribution validation rules](contributing.md).

Assign review by the unanswered question. One non-authoring reviewer may cover correctness and API quality; add another for specific uncovered expertise. Give reviewers the revision, intended endpoint and validation evidence, and require inspection of definitions. Restating the author's summary is not independent source review. A reviewer first checks the PR for another reviewer's unexpired `CLAIM` line, posts its own for the head, and ends with a `**APPROVE** at <sha> by <id>` or `**REQUEST_CHANGES** at <sha> by <id>` verdict line; a hold is a `HOLD` line with an owner and an expiry. [Verdicts, claims and holds](../../policy/review.md#verdicts-claims-and-holds) gives the formats and the coordinators' sweeps.

The [semantic-withdrawal cases](../history/case-studies.md) explain why hypotheses, adversary power and realizability need attention after successful Lean checking. They are historical diagnoses, not asserted defects in the reviewed snapshot. The circuit-synthesis case illustrates a concrete API review question: does simplifying construction preserve wire sharing and charge the actual gates?

## Queue approved work and keep its approval

A reviewer with write access who approves a PR queues the approved head in the same step. Open a
PR ready for review instead of holding reviewed work in `--draft` while `lean-checks` finishes:
once source review and the advisory notices are read (`PR advisory notices` completes in about a
minute, and `lean-checks` uploads the `lean-advisory-notices` artifact right after building and
linting affected modules), approve the head and pass `--wait 30` so the helper waits up to 30
minutes for `ci-checks` at that exact SHA, stops on failure or a discussion edit, and enqueues
without polling. Use `scripts/queue_pr.py` from a trusted checkout of current `main`, or an
isolated copy obtained from a pinned revision of current `main`. Keep the approved PR head; do not refresh its branch to get the
tool or execute the PR branch's copy. From any working directory, substitute the trusted script's
path and the target PR/head below; pass the repository explicitly when working from private scratch:

```bash
python3 /path/to/trusted-main/scripts/queue_pr.py <PR> <approved-head> \
  --repo cslib-community/cslib-frontier
```

The script refuses any other head, a draft, a stacked PR still based on another branch, a conflict and failed checks. It reads every page of check results for that commit before choosing the latest attempt from the required GitHub App; a later page cannot hide a failed or running rerun behind an older success. The reviewer does not queue when the approval names a hold; a request for human review is not a hold, but a maintainer's hold is. Do not start `--wait` while completing CI will produce unread notices or manual pages; [Approve and queue](../../AGENTS.md#approve-and-queue) gives the rule. Updating `main` does not upgrade an already-running copy; its owner stops an old waiter before replacing it after holds clear.

When another PR is already queued, `queue_pr.py` replays the live queue prefix ahead of the
approved head just before enqueueing (using the trusted checkout, `GIT_DIR` including a full bare
repository, or the current full clone) and refuses on a textual conflict or when a non-empty queue
cannot be replayed locally; wait for an earlier conflicting entry to land (and restack) or leave the
queue, then rerun. If active queue entries are ahead and the PR modifies high-fan-in
`CslibFrontier/` hub modules (`>= 500` transitive importers), `queue_pr.py` compares the modules
the PR rebuilds with the union of those the entries ahead already rebuild; every later group build
rebuilds them until the PR lands. While more than six entries are ahead and the PR adds at least
500 modules to that union, it refuses: rerun when the queue is shorter, or pass `--allow-hub` to
queue it now. Otherwise it prints an advisory rebuild notice on enqueue. `--hold-hubs` refuses a
hub PR behind any entry, so broad hub refactors can wait for an empty queue. Every run first
prints the number of entries ahead and a rough time to land (entries ahead × 14 minutes / 8
concurrent group builds, plus the PR's own build). A reviewer can also run the prefix check
standalone before enqueueing:

```bash
python3 scripts/queue_status.py prefix <PR> <approved-head>
```

This replays the current queue ahead of that head as successive squash merges. It reports the
conflicting files and the first prefix where each overlaps. GitHub can reorder the queue after
the snapshot. The check fetches missing Git objects, leaves branches and the queue untouched,
and exits 0 for a clean textual merge, 1 for a conflict and 2 for an incomplete check.

On every run, just before enqueueing, `queue_pr.py` also reads the PR's comments and submitted
reviews for review records: whole lines, outside fenced code blocks, with times written
`YYYY-MM-DDTHH:MMZ`. It refuses while a `HOLD owner=<id> until=<time> reason=<text>` line is in
force (`until` has not passed and its owner has posted no later `HOLD-RELEASED by=<id>
reason=<text>` line; `by=maintainer` or `by=SamuelSchlesinger` releases an `owner=maintainer`
hold); while another reviewer's `CLAIM review head=<approved-head> by=<id> until=<time>` is
unexpired (never more than 45 minutes after it was posted) and that reviewer has posted no
verdict at the head since; and when a `**REQUEST_CHANGES** at <approved-head>` verdict is not
followed by a later `**APPROVE**` at that head. A verdict is a post whose first non-empty line
begins with one of those two prefixes. Pass `--reviewer <your-id>` so that your own claim does
not block. Free-text holds cannot be parsed, so comments since the newest approval at the head
that say "hold" or "holding" outside a record are listed as an advisory to read before relying
on the enqueue. These refusals are a backstop, not the reviewer's check of the discussion.

For a dependency upgrade, a tender holding several approved heads can start one watcher at the
first new-pin `main` commit. Supply the individual PR numbers and the SHAs their reviews cover:

```bash
python3 scripts/queue_status.py cache-ready <landed-main-sha> <PR>@<approved-head> \
  <PR>@<approved-head> --wait 300
```

The watcher probes the configured Lake origins for the landed revision's published mapping.
If main CI coalesced that push, it also checks the five latest successful main pushes. A later
revision qualifies when its first-parent history includes the pin bump and its toolchain,
manifest and Lake configuration match. The watcher waits up to a minute between rounds. Set
`COMPLEXITYLIB_CACHE_URL` to watch a specific origin. It reports each held head, including
moved and closed PRs. A non-author rechecks discussion and remaining holds before using
`queue_pr.py`. Omit `--wait` for one probe. Exit 0 means the mapping was readable and the held
heads were reported, 1 means it was unavailable and 2 means the check could not complete.

Merge `main` into an approved PR only when it conflicts, needs a change on `main` to pass CI, or a lower stacked PR has landed; the merge queue already tests each PR on top of the current `main`. GitHub declines any push to the branch of a PR still in the merge queue, even when its entry is unmergeable, so whoever restacks a queued PR first removes it with **Remove from queue** on the PR page or the `dequeuePullRequest` command in [Restacks](../../AGENTS.md#restacks). Dequeueing merges nothing; a non-author queues the new head again under the rules below. After such a restack, `python3 scripts/check_restack.py <approved head> <new head>`, run from a checkout of current `origin/main` after `git fetch origin`, replays the approved change onto the new head's `main` and compares the result with the new head. For a PR approved while stacked on another branch, add `--approved-base <lower head at approval>`, even when the approved head had also merged a newer `main` than that head: the script then replays from the merge of the two, so `main`'s changes are not counted as the PR's own. When the replay and the new head match and CI passes, the approval carries over: post the result line, and the non-author who queues the new head reruns the command it names. Otherwise review the paths and diffs it prints. When the only conflicts are in the `mk_all` aggregates, `references.bib` or `manual/sources.md`, `python3 scripts/restack_mechanical.py <PR> --approved-head <approved head>` checks that the head is the approved change, merges with the drivers, writes the aggregates as `lake exe mk_all` would and runs this check, without running the PR's code, then prints the final check result and the `queue_pr.py` command for after CI. Report the unprefixed final result line. Output marked `approval pre-check` only verifies the existing head. It refuses any other conflict, pushes only with `--push` (and only if the check passes and the branch has not moved), and never queues or comments. When a hand restack shifts `#L` declaration anchors in maintained `manual/` pages, `python3 scripts/check_operator_manual.py --fix-anchors` repoints unambiguous `[Ns.name](File.lean#Ln)` headers before re-checking. See [Restacks](../../AGENTS.md#restacks).

A restack that only merges entries of `references.bib` or `manual/sources.md` needs no fresh review once `check_restack.py` reports it identical.

## Record evidence at the level of the claim

During ordinary edits, use MCP diagnostics or targeted
`scripts/build.sh <modules and representative clients> --wfail --iofail`. Use
`scripts/check.sh --quick --no-full-fallback` at local validation checkpoints. Status 3 means
the change needs focused checks plus hosted full validation; do not automatically retry with a
local full check. On a checkout where importing the entire library is expensive,
`scripts/check.sh --focused` defers the unchanged global smoke and axiom tests if no library
or test client imports them. It reports each omitted target and also returns 3 for unsupported
changes. Run full `scripts/check.sh` only when explicitly requested or hosted coverage
is unavailable, and do not duplicate successful CI covering the final revision. The local
[restored-source audit](troubleshooting.md#diagnose-warnings-that-only-ci-reports) recovers
warning/info logs and streams its count, worker mode, current source and elapsed time. It can repeat
elaboration on unchanged restored sources, so it belongs to validation rather than every edit.

| Outcome | Evidence to retain |
|---|---|
| A client compiles | Revision/diff, command or hosted job, outcome |
| The intended theorem is formalized | Definitions, statement, source mapping and model/nonvacuity review |
| An API is easier to use | Representative before/after client and validation |
| A task is complete | Original acceptance criteria and remaining broader objective |
| A change is ready to integrate | Final revision's validation and independent agent review, no open hold |
| A development step took a given time | Defined endpoints, timestamps and measurement convention |

The issue owns scope and remaining work; the PR owns the final change, validation and review. Link evidence instead of repeating it. Keep polling and internal coordination out of public records. Distinguish completed milestones from the broader objective. A coordinator with authority monitors a queued PR until it lands or receives a concrete disposition: queued work is not integrated work.

## Find ready, stalled and finished work

Three maintenance scripts read the repository through the GitHub REST API with an authenticated
`gh`, one call per page, and refuse to start when fewer than 500 calls remain on the account
(`--min-remaining`). Each prints Markdown, or JSON with `--json`, and exits 2 when GitHub could not
be read. Only the last two write, and only with `--apply`.

```bash
python3 scripts/tender_report.py
```

This lists PRs approved at their exact current head (an approving review of that commit or a
verdict line naming it) whose required checks passed, that GitHub reports mergeable, that are based
on `main` and that no unreleased, unexpired `HOLD` line covers, but that are not queued. It
separates those that need a person to read the thread: free-text hold wording or a request for
human review, any mention of queueing, sequencing or waiting after the approval (such as another
coordinator's note that it will verify a restack before queueing), an expired unswept `HOLD`, a
review claim still in its lease, an unanswered `REQUEST_CHANGES` at the head from another reviewer,
or an approval not written as a verdict line naming a non-author reviewer. It also lists approved
PRs blocked by checks, conflicts or holds; stacked PRs whose lower PR has landed, and approved PRs
whose head moved after the approval, which need a restack or `scripts/check_restack.py` first;
expired `HOLD` lines; review claims that expired without a verdict; and PRs released to
coordinators (`RELEASED`) that no one has taken over (`TAKEOVER`). The report never queues.
The non-author who queues still reads the PR and runs `queue_pr.py` as above.

```bash
python3 scripts/stale_notices.py
python3 scripts/stale_notices.py --apply --identity '<who is posting, as the first paragraph>'
```

The dry run lists draft PRs with no author push or comment for 7 days (`--draft-days`), issue
claims (`Owner:` or `Claimed by` lines) whose claimant has been silent for 3 days and that no open
PR references (`--claim-days`), and PRs whose latest verdict requests changes at the current head
with no push or author reply for 48 hours (`--changes-hours`). On the shared account every agent
posts as one login, so another agent's comment there counts as the author's; read a listed item
before acting on it. `--apply` posts one notice per item, ending with the marker
`<!-- stale-notice:KIND -->`; an item already noticed since its last activity (or within the last
24 hours) is skipped, so a rerun never posts twice for the same stall. `--draft-stalled` also
converts the listed change requests to drafts. The script closes nothing and takes nothing over:
the report says when 24 hours have passed since a notice with no response, after which
[Workers](../../AGENTS.md#workers), item 3, applies.

```bash
python3 scripts/branch_cleanup.py --delete merged --delete closed --older-than 14d
python3 scripts/branch_cleanup.py --delete merged --apply
python3 scripts/branch_cleanup.py --notice --identity '<who is posting>' --notice-issue <N>
python3 scripts/branch_cleanup.py --delete nopr --notice-issue <N> --apply
```

Every branch is the head of an open PR, the base of an open PR, the head of a merged PR, the head
of a PR closed unmerged, or no PR's head. The default branch, protected and merge-queue branches,
the head or base of any open PR, and a branch pushed to after its PR closed are never deleted.
Closed and no-PR branches are deleted only when their closing date or last commit is older than
`--older-than`. With `--apply` the script writes the plan to a JSON log in the system temporary
directory (`--log` chooses the path), lists the open PRs again, and deletes a branch only if its
ref still points at the planned commit and no open PR uses it. It prints a restore command per
deletion, which works while GitHub still has the commit: a PR's `refs/pull/` ref keeps it, but a
branch with no PR has no such ref, so keep the log (or fetch the commits) before deleting `nopr`
branches.

No-PR branches are announced first. `--notice` writes the notice as one or more Markdown files
(each under GitHub's comment size limit) listing every selected no-PR branch with its last commit
date, author and tip commit, and prints the `gh issue comment` command that posts each; it posts
nothing itself (`--notice-report` prints the Markdown table report to standard output). After the
notice has been up for `--notice-wait` (default 7d), `--delete nopr --notice-issue <N>` selects
only the branches a notice on issue N listed at their current tip and that no later comment there
names; a push changes the tip, so the branch is kept. `--delete nopr --apply` refuses to run
without `--notice-issue`.

## Interpret timing and transcript records

Commit times, provider completion durations, conversation spans, CI runtime and PR elapsed time measure different things. Concurrent sessions overlap; summed duration is not elapsed wall-clock time or human effort. The [timing chapter](../history/timings.md) retains units and denominators. Its selected runs and cases do not estimate an automation success rate or causal speedup.

For new records, retain the initial objective, task/session identities, parent-child links, source revisions, reviews, failed attempts and dispositions. Preserve emitted timestamps and define their event semantics before deriving durations. Retain appropriate excerpts and provenance. The [extraction methods](../history/methods.md) describe deduplication; [study design](../history/study-design.md) identifies evidence needed for comparisons. Desktop conversations remain absent, so this edition's historical corpus is explicitly incomplete.

[complexitylib]: ../sources.md#complexitylib

When using the hierarchy first-noise/payment and completed-preparation clients, keep
structural `Request HP.k` fixed and supply `HP.k_pos` where positivity is required.
Statistical precision indexes estimates and walk lengths independently; specializing
structure to precision does not identify a fixed recursive hierarchy. See the
[probabilistic workflow](probabilistic-workflows.md) for the quantitative contracts.

For genuine signed-stage review, inspect the actual normalized index and final structural
dispatch, inherited-terminal usage containment, and the single negative request in
`canonical_residual_bins_mean`. Finite cover/horizon hypotheses remain acceptance limits.
The [probabilistic workflow](probabilistic-workflows.md) separates this proved stage mean
from estimated-child induction and native resource objectives.

For estimated-child review, inspect `estimated_residual_bins_mean_error` and the actual
first-mean client linked from the [probabilistic workflow](probabilistic-workflows.md).
Check true-input bounded/canonical routing agreement, the estimated-left/canonical-right
product split, literal importance/midpoint factors and once-negative error accounting.
Finite absolute propagation does not discharge recursive relative budgets or the second
signal's full-terminal-rank maximum.
