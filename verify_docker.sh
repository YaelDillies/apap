#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CACHE="${COMPARATOR_WORK:-$HOME/.cache/comparator-verify}"
mkdir -p "$CACHE/home" "$CACHE/docker"

source "$HERE/comparator/versions.env"

PLATFORM=()
if [[ "$(uname -m)" != "x86_64" ]]; then
  echo "note: non-x86_64 host — using --platform linux/amd64 (requires QEMU, will be slow)"
  PLATFORM=(--platform linux/amd64)
fi

exec docker run --rm "${PLATFORM[@]}" \
  --volume "$HERE:/repo:ro,z" \
  --volume "$CACHE:/cache:z" \
  --env "COMPARATOR_WORK=/cache/docker" \
  --env "HOME=/cache/home" \
  "$UBUNTU_IMAGE" \
  bash -c "
    apt-get update -qq && apt-get install -y -qq curl git zstd ca-certificates build-essential
    mkdir /work
    tar -C /repo --exclude='.lake' --exclude='.git' -cf - . | tar -C /work -xf -
    cd /work
    bash /work/verify.sh
  "
