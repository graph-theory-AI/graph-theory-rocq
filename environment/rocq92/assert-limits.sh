#!/bin/sh
# Rocq 9.2 step (1) (arthur): fail the build step unless its container runs under the stated limits.
# Reads the build container's own cgroup v2 files (not host /proc). Usage: assert-limits.sh MEMORY_MAX "QUOTA PERIOD"
m=$(cat /sys/fs/cgroup/memory.max 2>/dev/null) || m=unread
c=$(cat /sys/fs/cgroup/cpu.max 2>/dev/null) || c=unread
echo "BUILD-LIMITS memory.max=$m cpu.max=$c"
[ "$m" = "$1" ] && [ "$c" = "$2" ] || { echo "REFUSED: build limits not applied (want memory.max=$1 cpu.max=$2)"; exit 1; }
