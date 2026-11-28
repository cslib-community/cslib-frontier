#!/usr/bin/env python3
"""Collect the public GitHub record behind the NL = UL postmortem (issue #6747).

Requires an authenticated `gh` CLI. Writes JSON caches and the plot tables
cum.dat and hourly.dat into the output directory (default: current directory).
The measurements in postmortem.tex are dated observations taken on 2026-11-22.
"""
import collections
import datetime as dt
import json
import re
import subprocess
import sys
from pathlib import Path

REPO = 'cslib-community/cslib-frontier'
ISSUE = 6747
T0 = dt.datetime(2026, 11, 20, 14, 57, 3, tzinfo=dt.timezone.utc)
WINDOW = (dt.datetime(2026, 11, 20, 14), dt.datetime(2026, 11, 22, 15))
OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('.')

PR_FIELDS = '''number title state createdAt mergedAt closedAt author{login}
additions deletions changedFiles headRefName baseRefName bodyText
commits{totalCount} reviews{totalCount} comments{totalCount}
files(first:100){nodes{path additions deletions}}
timelineItems(first:100,itemTypes:[HEAD_REF_FORCE_PUSHED_EVENT,BASE_REF_CHANGED_EVENT,
  ADDED_TO_MERGE_QUEUE_EVENT,REMOVED_FROM_MERGE_QUEUE_EVENT,MERGED_EVENT,CLOSED_EVENT]){
  nodes{__typename ... on RemovedFromMergeQueueEvent{createdAt reason}}}'''


def gh(*args):
    return json.loads(subprocess.run(['gh', *args], check=True, capture_output=True,
                                     text=True).stdout)


def ts(s):
    return dt.datetime.fromisoformat(s.replace('Z', '+00:00'))


def hours(s):
    return (ts(s) - T0).total_seconds() / 3600


def main():
    issue = gh('issue', 'view', str(ISSUE), '-R', REPO, '--json', 'body,createdAt,closedAt')
    comments = gh('api', '--paginate', f'repos/{REPO}/issues/{ISSUE}/comments')
    text = issue['body'] + '\n'.join(c['body'] for c in comments)
    nums = {int(n) for n in re.findall(r'cslib-frontier/(?:pull|issues)/(\d+)', text)}
    nums |= {int(n) for n in re.findall(r'(?<![\w/])#(\d{4})\b', text)}
    nums |= {x['number'] for x in gh('search', 'prs', '--repo', REPO, str(ISSUE),
                                      '--limit', '300', '--json', 'number')}
    nums = sorted(n for n in nums if 5000 < n < 8000 and n != ISSUE)

    prs = {}
    for k in range(0, len(nums), 10):
        body = ' '.join(f'p{n}:pullRequest(number:{n}){{{PR_FIELDS}}}' for n in nums[k:k + 10])
        q = f'query{{repository(owner:"cslib-community",name:"cslib-frontier"){{{body}}}}}'
        data = gh('api', 'graphql', '-f', f'query={q}').get('data') or {}
        for v in (data.get('repository') or {}).values():
            if v:
                prs[v['number']] = v

    runs = {}
    t = WINDOW[0]
    while t < WINDOW[1]:
        u = t + dt.timedelta(hours=2)
        page = 1
        while True:
            q = f'created={t:%Y-%m-%dT%H:%M:%SZ}..{u:%Y-%m-%dT%H:%M:%SZ}'
            r = gh('api', f'repos/{REPO}/actions/runs?{q}&per_page=100&page={page}')
            for w in r['workflow_runs']:
                runs[w['id']] = {k: w[k] for k in ('id', 'name', 'event', 'head_branch',
                                 'conclusion', 'created_at', 'run_started_at', 'updated_at')}
            if len(r['workflow_runs']) < 100 or page * 100 >= min(r['total_count'], 1000):
                break
            page += 1
        t = u

    for name, obj in (('comments', comments), ('prs', prs), ('runs', list(runs.values()))):
        (OUT / f'{name}.json').write_text(json.dumps(obj))

    heads = {x['headRefName']: x['number'] for x in prs.values()}

    def run_pr(r):
        b = r['head_branch'] or ''
        if b in heads:
            return heads[b]
        m = re.match(r'gh-readonly-queue/main/pr-(\d+)-', b)
        return int(m.group(1)) if m and int(m.group(1)) in prs else None

    opened = [hours(x['createdAt']) for x in prs.values()]
    merged = [hours(x['mergedAt']) for x in prs.values() if x['mergedAt']]
    with open(OUT / 'cum.dat', 'w') as f:
        f.write('h opened merged\n')
        for h in range(49):
            f.write(f'{h} {sum(v <= h for v in opened)} {sum(v <= h for v in merged)}\n')
    per_hour = collections.Counter(int(hours(c['created_at'])) for c in comments)
    lean = collections.defaultdict(float)
    for r in runs.values():
        if r['name'] == 'Lean Action CI' and run_pr(r) and r['run_started_at']:
            lean[int(hours(r['run_started_at']))] += max(
                0, (ts(r['updated_at']) - ts(r['run_started_at'])).total_seconds() / 3600)
    with open(OUT / 'hourly.dat', 'w') as f:
        f.write('h comments leanmin\n')
        for h in range(48):
            f.write(f'{h} {per_hour.get(h, 0)} {lean.get(h, 0):.1f}\n')
    print(f'{len(prs)} PRs, {len(comments)} comments, {len(runs)} runs')


if __name__ == '__main__':
    main()
