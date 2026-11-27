#!/bin/sh
# THE PARSER'S SANDBOX (27 Nov, red team 14:20Z/14:21Z). Run as root by the read job, with an empty environment:
#   sudo -n /usr/bin/env -i PATH=/usr/bin:/bin /bin/sh tools/read-sandbox.sh <jail> <judge blob>
# <jail> holds tools/read-decision.py, tools/outside-read.py and in/proof.lean, read only. In new network, IPC, UTS, PID
# and mount namespaces: the jail is bind-mounted read-only at /jail, and every place a job keeps files (the runner's
# home and workspace, its control files, /opt, /usr/local, /tmp, /var, /root, /mnt, /srv, /run) is covered by an empty
# tmpfs, so the parser sees the runtime under /usr and /etc, the jail, and nothing else. Then nobody, no new
# privileges, no capabilities, limits, a clean environment, and python3 -I -S. Prints only what the parser prints.
set -eu
[ "$#" = 2 ] && [ -d "$1" ] || exit 2
printf '%s' "$2" | grep -Eqx '[0-9a-f]{40}' || exit 2
mkdir -p /jail
exec /usr/bin/unshare --net --ipc --uts --pid --fork --mount --mount-proc -- /bin/sh -eu -c '
  mount --make-rprivate /
  mount --bind "$1" /jail
  mount -o remount,bind,ro,nosuid,nodev /jail
  for d in /home /opt /usr/local /tmp /var /root /mnt /srv /run /media; do
    if [ -d "$d" ]; then mount -t tmpfs -o size=8m,mode=0755,nosuid,nodev tmpfs "$d"; fi
  done
  exec /usr/bin/setpriv --reuid=65534 --regid=65534 --clear-groups --no-new-privs --inh-caps=-all --bounding-set=-all -- \
    /usr/bin/prlimit --as=1073741824 --cpu=60 --fsize=65536 --nofile=64 --nproc=64 --core=0 -- \
    /usr/bin/env -i PATH=/usr/bin:/bin LANG=C.UTF-8 \
    /usr/bin/timeout -s KILL 90 /usr/bin/python3 -I -S /jail/tools/read-decision.py /jail/in/proof.lean "$2"
' sh "$1" "$2"
