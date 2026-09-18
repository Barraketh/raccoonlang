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
mathlib_tag="v${lean_version}"
mathlib_commit="c5ea00351c28e24afc9f0f84379aa41082b1188f"
mathlib_dir="${repo_root}/temp/mathlib-${mathlib_tag}"
artifact_dir="${repo_root}/artifacts/lean/${exporter_tag}"

init_prelude_sha256="802e80820fe7b48f475182851f6c2385e647691596a45a8ed312b3e8e3ce452f"
init_sha256="75b2cb000d698aac2946ea76d3401d5939c9274ebd7849d1b46f25ee2fcd28d9"
mathlib_logic_basic_sha256="be0803746160ed431cc077e7af6c3c7bc5831a5df3623a1da23ad8ac2a7c58dd"
init_lossless_sha256="4e71a266e496248a986f95ed1f7c5b18107cac767115650c73083eaba42f594a"
mathlib_logic_basic_lossless_sha256="114ff3afa7ca12421a1dda30f7f8ce797985a4052daee7716c7322e1dac4798c"

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

if [[ ! -d "${mathlib_dir}/.git" ]]; then
  git clone --depth 1 --branch "${mathlib_tag}" \
    https://github.com/leanprover-community/mathlib4.git "${mathlib_dir}"
fi

actual_mathlib_commit=$(git -C "${mathlib_dir}" rev-parse HEAD)
if [[ "${actual_mathlib_commit}" != "${mathlib_commit}" ]]; then
  echo "${mathlib_dir} is at ${actual_mathlib_commit}; expected ${mathlib_commit}" >&2
  exit 1
fi

(
  cd "${exporter_dir}"
  elan run "${lean_toolchain}" lake build
)

elan run "${lean_toolchain}" lean --run "${script_dir}/validate-k6-mdata-profile.lean"

mkdir -p "${artifact_dir}"

generate_artifact() (
  local module_name=$1
  local expected_sha256=$2
  local output_name=${3:-${module_name}}
  local exporter_option=${4:-}
  local destination="${artifact_dir}/${output_name}.ndjson"

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
  trap 'rm -f -- "${temporary_file}"' EXIT
  (
    cd "${exporter_dir}"
    if [[ -n "${exporter_option}" ]]; then
      elan run "${lean_toolchain}" lake env .lake/build/bin/lean4export \
        "${exporter_option}" "${module_name}" >"${temporary_file}"
    else
      elan run "${lean_toolchain}" lake env .lake/build/bin/lean4export "${module_name}" >"${temporary_file}"
    fi
  )

  local actual_sha256
  actual_sha256=$(shasum -a 256 "${temporary_file}" | awk '{print $1}')
  if [[ "${actual_sha256}" != "${expected_sha256}" ]]; then
    echo "${module_name} SHA-256 is ${actual_sha256}, expected ${expected_sha256}" >&2
    exit 1
  fi
  mv "${temporary_file}" "${destination}"
  trap - EXIT
  echo "wrote ${destination}"
)

generate_artifact "Init.Prelude" "${init_prelude_sha256}"
generate_artifact "Init" "${init_sha256}"
generate_artifact "Init" "${init_lossless_sha256}" "Init.lossless" "--export-mdata"

generate_mathlib_artifact() (
  local module_name=$1
  local expected_sha256=$2
  local output_name=${3:-${module_name}}
  local exporter_option=${4:-}
  local destination="${artifact_dir}/${output_name}.ndjson"

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

  (
    cd "${mathlib_dir}"
    elan run "${lean_toolchain}" lake exe cache get "${module_name//.//}.lean"
  )

  local temporary_file
  temporary_file=$(mktemp "${artifact_dir}/.${module_name}.ndjson.XXXXXX")
  trap 'rm -f -- "${temporary_file}"' EXIT
  (
    cd "${mathlib_dir}"
    if [[ -n "${exporter_option}" ]]; then
      elan run "${lean_toolchain}" lake env "${exporter_dir}/.lake/build/bin/lean4export" \
        "${exporter_option}" "${module_name}" >"${temporary_file}"
    else
      elan run "${lean_toolchain}" lake env "${exporter_dir}/.lake/build/bin/lean4export" \
        "${module_name}" >"${temporary_file}"
    fi
  )

  local actual_sha256
  actual_sha256=$(shasum -a 256 "${temporary_file}" | awk '{print $1}')
  if [[ "${actual_sha256}" != "${expected_sha256}" ]]; then
    echo "${module_name} SHA-256 is ${actual_sha256}, expected ${expected_sha256}" >&2
    exit 1
  fi
  mv "${temporary_file}" "${destination}"
  trap - EXIT
  echo "wrote ${destination}"
)

generate_mathlib_artifact "Mathlib.Logic.Basic" "${mathlib_logic_basic_sha256}"
generate_mathlib_artifact "Mathlib.Logic.Basic" "${mathlib_logic_basic_lossless_sha256}" \
  "Mathlib.Logic.Basic.lossless" "--export-mdata"

echo "Lean and Mathlib artifacts are verified for ${lean_toolchain} (${lean_commit})."
