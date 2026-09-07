#!/usr/bin/env bash

set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "${repo_root}"
cache_dir="${repo_root}/.reference-cache"
paper_dir="${cache_dir}/papers"
web_dir="${cache_dir}/web"
repo_dir="${cache_dir}/repos"
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/erdos81-references.XXXXXX")
trap 'rm -rf -- "${tmp_dir}"' EXIT

mkdir -p \
  "${paper_dir}/traverso" \
  "${paper_dir}/cipollini/source" \
  "${web_dir}" \
  "${repo_dir}"

# The concept DOI can acquire new versions.  Record 22064657 is the immutable
# v3 snapshot inspected for this project.
zenodo_record=22064657
zenodo_api="https://zenodo.org/api/records/${zenodo_record}"
curl -L --fail --silent --show-error \
  "${zenodo_api}" \
  -o "${web_dir}/traverso-zenodo-record-2026-09-07.json"

for filename in \
  PAPER_I_preprint_v1.3_en.pdf \
  PAPER_II_preprint_v1.2_en.pdf \
  PAPER_III_preprint_v1.5_en.pdf
do
  curl -L --fail --silent --show-error \
    "${zenodo_api}/files/${filename}/content" \
    -o "${paper_dir}/traverso/${filename}"
done

# Resolve the public Overleaf read token to a project identifier.  The source
# link is mutable, so the expected archive digest below is deliberately strict.
overleaf_token=thjptfhgnmxc
overleaf_hash='#cc1388'
overleaf_page="${tmp_dir}/overleaf.html"
overleaf_cookies="${tmp_dir}/cookies.txt"
overleaf_grant="${tmp_dir}/grant.json"

curl -L --fail --silent --show-error \
  -c "${overleaf_cookies}" \
  "https://www.overleaf.com/read/${overleaf_token}" \
  -o "${overleaf_page}"

csrf=$(sed -n 's/.*name="ol-csrfToken" content="\([^"]*\)".*/\1/p' "${overleaf_page}")
if [[ -z "${csrf}" ]]; then
  echo "Could not extract the Overleaf CSRF token." >&2
  exit 1
fi

curl --fail --silent --show-error \
  -b "${overleaf_cookies}" \
  -c "${overleaf_cookies}" \
  -H 'Content-Type: application/json' \
  -H "X-CSRF-Token: ${csrf}" \
  --data "{\"confirmedByUser\":false,\"tokenHashPrefix\":\"${overleaf_hash}\"}" \
  "https://www.overleaf.com/read/${overleaf_token}/grant" \
  -o "${overleaf_grant}"

project_id=$(python3 -c \
  'import json, pathlib; print(pathlib.PurePosixPath(json.load(open(__import__("sys").argv[1]))["redirect"]).name)' \
  "${overleaf_grant}")

cipollini_zip="${paper_dir}/cipollini/overleaf-project-2026-09-07.zip"
curl -L --fail --silent --show-error \
  -b "${overleaf_cookies}" \
  "https://www.overleaf.com/project/${project_id}/download/zip" \
  -o "${cipollini_zip}"
unzip -t "${cipollini_zip}"
unzip -o "${cipollini_zip}" -d "${paper_dir}/cipollini/source"

traverso_commit=cdd0b98c0c663b98e1be020b4ef23becc50d22e5
traverso_repo="${repo_dir}/traverso"
if [[ ! -d "${traverso_repo}/.git" ]]; then
  git clone https://github.com/jtraverso/erdos-81-chordal-clique-partitions.git \
    "${traverso_repo}"
fi
git -C "${traverso_repo}" fetch origin "${traverso_commit}"
git -C "${traverso_repo}" checkout --detach "${traverso_commit}"

reconstruction_commit=419d639395bd5e3bc32f7e6e220a6c2c371e1ea5
reconstruction_repo="${repo_dir}/reconstruction-conjecture"
if [[ ! -d "${reconstruction_repo}/.git" ]]; then
  git clone https://github.com/SamuelSchlesinger/reconstruction-conjecture.git \
    "${reconstruction_repo}"
fi
git -C "${reconstruction_repo}" fetch origin "${reconstruction_commit}"
git -C "${reconstruction_repo}" checkout --detach "${reconstruction_commit}"

cat <<'DIGESTS' | sha256sum --check
37626b68bfc9c908b9e08ac563635cb422e68369e1f4aacda1b7dd9e71716fb6  .reference-cache/papers/traverso/PAPER_I_preprint_v1.3_en.pdf
67bf3490cab8c54356850215a739b92a8007e48509707f64f622d5f6b402f4eb  .reference-cache/papers/traverso/PAPER_II_preprint_v1.2_en.pdf
077a12da4db42ecbe6bcc25333539bf7ee3e63fa20bc7a46d8e801120ac9bb27  .reference-cache/papers/traverso/PAPER_III_preprint_v1.5_en.pdf
ed61b083e68b0bb111d0b5e5c063dc57fe0e01d83783d88ba5ab890d84eacefe  .reference-cache/papers/cipollini/overleaf-project-2026-09-07.zip
DIGESTS

echo "Reference cache populated at ${cache_dir}"
echo "Traverso repository commit: $(git -C "${traverso_repo}" rev-parse HEAD)"
echo "Chordal Lean comparison commit: $(git -C "${reconstruction_repo}" rev-parse HEAD)"
