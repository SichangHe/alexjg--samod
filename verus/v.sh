#!/bin/sh
# usage: v.sh [file]  (default samod_verified.rs)
cd "$(dirname "$0")"
"${VERUS:-verus}" --crate-type lib --triggers-mode silent "${1:-samod_verified.rs}" 2>&1
