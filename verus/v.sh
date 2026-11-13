#!/bin/sh
# usage: v.sh [file]  (default samod_verified.rs)
cd "$(dirname "$0")"
/hdd1/sichangheagent/vl_meeting_work/tools/verus-x86-linux/verus --crate-type lib --triggers-mode silent "${1:-samod_verified.rs}" 2>&1
