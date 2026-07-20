#!/usr/bin/env bash

set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(CDPATH= cd -- "${script_dir}/.." && pwd)

lean_version="4.30.0"
lean_commit="d024af099ca4bf2c86f649261ebf59565dc8c622"
lean_toolchain="leanprover/lean4:v${lean_version}"
exporter_tag="v${lean_version}"
exporter_commit="a3e35a584f59b390667db7269cd37fca8575e4bf"
exporter_dir="${repo_root}/temp/lean4export-${exporter_tag}"
artifact_dir="${repo_root}/artifacts/lean/${exporter_tag}"

init_prelude_sha256="802e80820fe7b48f475182851f6c2385e647691596a45a8ed312b3e8e3ce452f"
init_sha256="75b2cb000d698aac2946ea76d3401d5939c9274ebd7849d1b46f25ee2fcd28d9"

for command_name in elan git shasum; do
  if ! command -v "${command_name}" >/dev/null 2>&1; then
    echo "missing required command: ${command_name}" >&2
    exit 1
  fi
done

if ! elan toolchain list | grep -Fqx "${lean_toolchain}"; then
  elan toolchain install "${lean_toolchain}"
fi
lean_banner=$(elan run "${lean_toolchain}" lean --version)
if [[ "${lean_banner}" != *"version ${lean_version}"* || "${lean_banner}" != *"commit ${lean_commit}"* ]]; then
  echo "installed Lean does not match ${lean_version} at ${lean_commit}: ${lean_banner}" >&2
  exit 1
fi

if [[ ! -d "${exporter_dir}/.git" ]]; then
  git clone --depth 1 --branch "${exporter_tag}" \
    https://github.com/leanprover/lean4export.git "${exporter_dir}"
fi

actual_exporter_commit=$(git -C "${exporter_dir}" rev-parse HEAD)
if [[ "${actual_exporter_commit}" != "${exporter_commit}" ]]; then
  echo "${exporter_dir} is at ${actual_exporter_commit}; expected ${exporter_commit}" >&2
  exit 1
fi

(
  cd "${exporter_dir}"
  elan run "${lean_toolchain}" lake build
)

mkdir -p "${artifact_dir}"

generate_artifact() {
  local module_name=$1
  local expected_sha256=$2
  local destination="${artifact_dir}/${module_name}.ndjson"

  if [[ -f "${destination}" ]]; then
    local existing_sha256
    existing_sha256=$(shasum -a 256 "${destination}" | awk '{print $1}')
    if [[ "${existing_sha256}" == "${expected_sha256}" ]]; then
      echo "reusing verified ${destination}"
      return
    fi
    echo "refusing to overwrite ${destination}: SHA-256 is ${existing_sha256}, expected ${expected_sha256}" >&2
    exit 1
  fi

  local temporary_file
  temporary_file=$(mktemp "${artifact_dir}/.${module_name}.ndjson.XXXXXX")
  (
    cd "${exporter_dir}"
    elan run "${lean_toolchain}" lake env .lake/build/bin/lean4export "${module_name}" >"${temporary_file}"
  )

  local actual_sha256
  actual_sha256=$(shasum -a 256 "${temporary_file}" | awk '{print $1}')
  if [[ "${actual_sha256}" != "${expected_sha256}" ]]; then
    echo "${module_name} SHA-256 is ${actual_sha256}, expected ${expected_sha256}" >&2
    exit 1
  fi
  mv "${temporary_file}" "${destination}"
  echo "wrote ${destination}"
}

generate_artifact "Init.Prelude" "${init_prelude_sha256}"
generate_artifact "Init" "${init_sha256}"

echo "Lean artifacts are verified for ${lean_toolchain} (${lean_commit})."
