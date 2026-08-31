#!/usr/bin/env bash
set -euo pipefail

# The route packages resolve `../../../.lake-packages` to this workspace root.
# A single root link therefore lets both Algebraic Jacobian routes share
# Horizon's pinned package checkouts and compiled dependency artifacts without
# putting those artifacts in this repository.
workspace_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
horizon_root="${1:-${LEAN_ALGEBRAIC_GEOMETRY_HORIZON:-/home/axel/LeanAlgebraicGeometry-Horizon}}"
source_dir="${horizon_root}/.lake-packages"
target_dir="${workspace_root}/.lake-packages"

if [[ ! -d "${source_dir}" ]]; then
  printf 'Horizon package directory not found: %s\n' "${source_dir}" >&2
  printf 'Pass the Horizon checkout as the first argument or set LEAN_ALGEBRAIC_GEOMETRY_HORIZON.\n' >&2
  exit 1
fi

source_real="$(readlink -f -- "${source_dir}")"

if [[ -L "${target_dir}" ]]; then
  target_real="$(readlink -f -- "${target_dir}")"
  if [[ "${target_real}" == "${source_real}" ]]; then
    printf 'Shared Lake package cache already linked: %s\n' "${target_dir}"
    exit 0
  fi
  printf 'Refusing to replace existing cache link: %s -> %s\n' "${target_dir}" "${target_real}" >&2
  exit 1
fi

if [[ -e "${target_dir}" ]]; then
  if [[ -d "${target_dir}" ]] && [[ -z "$(find "${target_dir}" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
    rmdir -- "${target_dir}"
  else
    printf 'Refusing to replace non-empty cache directory: %s\n' "${target_dir}" >&2
    printf 'Move it aside manually if you want to use the shared Horizon cache.\n' >&2
    exit 1
  fi
fi

ln -s -- "${source_real}" "${target_dir}"
printf 'Linked shared Lake package cache: %s -> %s\n' "${target_dir}" "${source_real}"
