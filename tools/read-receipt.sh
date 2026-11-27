#!/bin/bash
# THE READ RECEIPT (27 Nov), the authoritative workflow's `read` job, after the parse. Our values only:
#   read-receipt.sh <decision.json> <proof.lean> <in dir> <base checkout> <receipt.json out>
# with GITHUB_REPOSITORY, PR, GITHUB_RUN_ID, GITHUB_RUN_ATTEMPT and GITHUB_SHA set by the runner (PR validated by the
# job's first step). The decision line from the sandboxed parse is taken only when it is ONE line of at most 8192 bytes
# whose every field is a word of read-decision.py --vocab (run here with no data); anything else becomes the fixed
# HOLD with the shape code ERROR. The file's sha256 is computed here, never by the parse. Prints one line:
#   READ-RECEIPT sha256=<sha256 of receipt.json> decision=<PLAIN|UNION|HOLD>
set -eu
d=$1; f=$2; in=$3; base=$4; out=$5
blob=$(cat "$in/pr.blob"); head=$(cat "$in/pr.head"); path=$(cat "$in/pr.file")
printf '%s %s %s %s %s' "$PR" "$GITHUB_RUN_ID" "$GITHUB_RUN_ATTEMPT" "$GITHUB_SHA" "$GITHUB_REPOSITORY" \
  | grep -Eqx '[1-9][0-9]{0,6} [1-9][0-9]{0,15} [1-9][0-9]{0,3} [0-9a-f]{40} [A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+' || { echo "READ-JOB: malformed run values; no receipt"; exit 1; }
printf '%s %s' "$blob" "$head" | grep -Eqx '[0-9a-f]{40} [0-9a-f]{40}' || { echo "READ-JOB: malformed identity; no receipt"; exit 1; }
printf '%s' "$path" | grep -Eqx 'lean/PEqualNP/Outside/[A-Za-z0-9_]{1,200}\.lean' || { echo "READ-JOB: malformed path; no receipt"; exit 1; }
[ "$(git hash-object "$f")" = "$blob" ] || { echo "READ-JOB: the bytes are not the named blob; no receipt"; exit 1; }
sha=$(sha256sum "$f" | cut -d' ' -f1)
vocab=$(mktemp); python3 -I "$base/tools/read-decision.py" --vocab > "$vocab"
ok=no
if [ -f "$d" ] && [ "$(wc -l < "$d")" -eq 1 ] && [ "$(wc -c < "$d")" -le 8192 ] && jq -e --slurpfile v "$vocab" '
     def tok: type == "string" and (. as $t | $v[0].tokens | index([$t]) != null);
     def code: type == "string" and length <= 64 and (split("+") | length >= 1 and all(. as $c | $v[0].codes | index([$c]) != null));
     (.shapes | if type == "array" then length else 0 end) as $n
     | (keys == ["authorized","classes","classifier","decision","nshapes","shapes"])
     and .classifier == $v[0].classifier and .authorized == $v[0].authorized
     and (.decision | IN("PLAIN","UNION","HOLD"))
     and (.classes | type == "array" and length <= 4 and all(. as $c | $v[0].authorized | index([$c]) != null))
     and (.shapes | type == "array" and length <= $v[0].max_shapes
          and all(type == "array" and length == 4 and (.[0] | type == "number" and . >= 0 and . <= $v[0].max_count and floor == .)
                  and (.[1] | code) and (.[2] | tok) and (.[3] | tok)))
     and (.nshapes | type == "number" and . >= $n and . <= $v[0].max_count and floor == .)
     and ((.decision == "PLAIN" and .classes == [] and .shapes == [])
          or (.decision == "UNION" and (.classes | length) >= 1 and .shapes == [])
          or (.decision == "HOLD" and .classes == [] and (.shapes | length) >= 1))' "$d" > /dev/null 2>&1; then ok=yes; fi
if [ "$ok" = yes ]; then dec=$(jq -c . "$d"); else
  dec=$(jq -cn --slurpfile v "$vocab" '{classifier: $v[0].classifier, authorized: $v[0].authorized, decision: "HOLD", classes: [], shapes: [[0, "ERROR", "empty", "empty"]], nshapes: 1}')
fi
clsha=$(cat "$base/tools/read-decision.py" "$base/tools/outside-read.py" | sha256sum | cut -d' ' -f1)
wfsha=$(git -C "$base" rev-parse HEAD:.github/workflows/authoritative.yml)
printf '%s' "$dec" | jq -cS --arg repo "$GITHUB_REPOSITORY" --argjson pr "$PR" --arg head "$head" --arg path "$path" --arg blob "$blob" \
  --arg sha "$sha" --argjson run "$GITHUB_RUN_ID" --argjson attempt "$GITHUB_RUN_ATTEMPT" --arg base "$GITHUB_SHA" --arg wf "$wfsha" --arg clsha "$clsha" \
  '{v: 1, job: "read", repo: $repo, pr: $pr, head: $head, path: $path, blob: $blob, sha256: $sha, run_id: $run, run_attempt: $attempt,
    base: $base, workflow_blob: $wf, classifier: .classifier, classifier_sha256: $clsha, authorized: .authorized,
    decision: .decision, classes: .classes, shapes: .shapes, nshapes: .nshapes}' > "$out"
rm -f "$vocab"
echo "READ-RECEIPT sha256=$(sha256sum "$out" | cut -d' ' -f1) decision=$(jq -r .decision "$out")"
