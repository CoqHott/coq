#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

GeoCoq_CI_DIR="${CI_BUILD_DIR}/GeoCoq"

git_checkout "${GeoCoq_CI_BRANCH}" "${GeoCoq_CI_GITURL}" "${GeoCoq_CI_DIR}"

install_ssralg

( cd "${GeoCoq_CI_DIR}" && \
  sed  -i '1i Set Nested Proofs Allowed.' Meta_theory/Models/hilbert_to_tarski.v && \
  ./configure.sh && make )
