#!/usr/bin/env bash
# Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Christian Reitwiessner
# Reclaim unused SDK space before restoring Lean caches on ephemeral hosted runners.
set -euo pipefail

if [[ "${GITHUB_ACTIONS:-}" != true || "${RUNNER_ENVIRONMENT:-}" != github-hosted ||
      "${RUNNER_OS:-}" != Linux ]]; then
  echo "Skipping SDK cleanup outside GitHub-hosted Linux runners."
  exit 0
fi

df -h / || true
# Operators can calibrate this against the peak disk samples in completed job summaries.
# Standard ubuntu-24.04 runners start with ~88-89 GiB free on `/`, while `.lake`, the Lean
# toolchain and temporary handoff/publication staging peak under 30 GiB; 60 GiB skips the 60-85s
# SDK wipe on standard runners while retaining >30 GiB headroom and cleaning smaller images.
minimum_gib=${SDK_CLEANUP_MIN_GIB:-60}
if [[ ! "$minimum_gib" =~ ^[1-9][0-9]{0,3}$ ]]; then
  echo "Invalid SDK_CLEANUP_MIN_GIB; using 60 GiB."
  minimum_gib=60
fi
available_kib=
if disk_report=$(df -Pk /); then
  read -r _ _ _ available_kib _ <<< "${disk_report##*$'\n'}"
fi
if [[ "$available_kib" =~ ^[0-9]+$ ]] && (( available_kib >= minimum_gib * 1024 * 1024 )); then
  echo "Skipping SDK cleanup: at least ${minimum_gib} GiB is already available."
  exit 0
fi
# If the space query fails or cannot be parsed, retain the existing cleanup behavior.
# These preinstalled SDKs are not used by Lean, Python or the workflow's Node actions.
# Keep the tool cache, compiler, repository, Lean toolchain and build caches intact.
sudo rm -rf -- /usr/local/lib/android /usr/share/dotnet
df -h / || true
