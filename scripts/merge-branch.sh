#!/usr/bin/env bash
# Merge an agent branch into the current branch safely in this jj-colocated repo.
# - union-resolves conflicts in append-only docs (docs/PERF.md), stops on any other conflict
# - re-stages every path the branch touched right before committing (jj's watchman trigger can
#   reset the git index mid-merge), then verifies every file the branch added exists in HEAD.
set -euo pipefail
b="$1"; msg="${2:-merge: $1}"
base=$(git merge-base HEAD "$b")
if ! out=$(git merge --no-ff --no-commit "$b" 2>&1); then
  if [ -z "$(git diff --name-only --diff-filter=U)" ]; then echo "merge failed: $out"; exit 3; fi
fi
conf=$(git diff --name-only --diff-filter=U || true)
for f in $conf; do
  case "$f" in
    docs/PERF.md|docs/perf/history.jsonl|docs/perf/budgets.toml|docs/perf/latest.md)
      python3 - "$f" <<'PY'
import sys
p=sys.argv[1]; lines=open(p).read().split('\n')
out=[l for l in lines if not (l.startswith('<<<<<<< ') or l=='=======' or l.startswith('>>>>>>> ') or l.startswith('||||||| '))]
open(p,'w').write('\n'.join(out))
PY
      git add "$f";;
    *) echo "CONFLICT (manual): $f"; exit 2;;
  esac
done
# re-stage everything the branch changed relative to the merge base
git diff --name-only --diff-filter=AMR "$base" "$b" | while read -r f; do if [ -e "$f" ]; then git add -- "$f"; fi; done
git diff --name-only --diff-filter=D "$base" "$b" | while read -r f; do git rm -q --cached --ignore-unmatch -- "$f" >/dev/null || true; done
git commit -q -m "$msg

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
missing=0
for f in $(git diff --name-only --diff-filter=A "$base" "$b"); do
  git cat-file -e "HEAD:$f" 2>/dev/null || { echo "MISSING in HEAD: $f"; missing=1; }
done
[ "$missing" = 0 ] && echo "merged $b OK ($(git rev-parse --short HEAD))"
