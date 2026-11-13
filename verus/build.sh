#!/bin/sh
# samod_verified.rs = vlm45 model (model_base.rs, verbatim copy of out/vlm45_amproof/proto_fix_live2.rs) + parts 11-14
cd "$(dirname "$0")" && cat model_base.rs part11.rs part11b.rs part12.rs part13.rs part14.rs > samod_verified.rs && ./v.sh
