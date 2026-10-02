# Native Cursor Cloud environment Build evidence

This file records native Cursor Build evidence only. It does not claim that the
separate Morpho proof task succeeded.

## Environment and initial Build

- Environment: `9e913d70-be66-11f1-bb68-864e54d14197`
- Initial environment version: `9fb5caa8-be66-11f1-bb68-864e54d14197`
- Initial recurring Build: `bld-20261002-a309b12f-e20a-4989-8968-d2781a34df2f`
- Build environment version: `2021262`
- Created/completed: `2026-10-02T13:39:01.835Z` /
  `2026-10-02T13:41:20.796Z`
- Cursor status: `SUCCEEDED`, but environment acceptance: **failed**

The complete native Build log shows that Cursor cloned `origin/master`, then ran
only Cursor's system setup commands. It never started a Docker build, never ran
`scripts/setup.sh`, and never mentioned Lean, Lake, Verity, solc, or either
Midnight module. An agent booted from this Build had no
`/etc/morpho-proof-environment`, `lean`, or `lake`.

Root cause: `.cursor/environment.json`, `.cursor/Dockerfile`, and
`scripts/setup.sh` existed only on `cursor/proof-sandbox`; Cursor's first
recurring Build prepared the repository default branch (`master`), where those
files did not exist. The Build's `SUCCEEDED` status therefore meant only that
the default Cursor image was snapshotted successfully.

## First branch-ref draft Build

- Draft Build: `bld-20261002-a419557b-8e05-4994-ace0-d9a7ef83249f`
- Build environment version: `2021263`
- Source/trigger: `AGENT` / `MANUAL`
- Created/completed: `2026-10-02T13:40:23.049Z` /
  `2026-10-02T13:48:58.879Z`
- Status: `SUCCEEDED`

This native Build used the feature-branch repository configuration. Its complete
log records:

- `Started: Docker build` and `Docker build completed` with exit code 0.
- Lean `4.31.0` and Lake `5.0.0`, installed by `.cursor/Dockerfile`.
- Docker step 6 writing `morpho-lean-v4.31.0` to
  `/etc/morpho-proof-environment`.
- Verity checked out at
  `9b472a8a48a9990337845f1720a20f374fa1e9cd`.
- Checksum-pinned solc `0.8.34+commit.80d5c536` installed at
  `.lake/solidity-import/solc-0.8.34`.
- `Built Midnight.Import`, `Built Midnight.Spec`, and
  `Build completed successfully (38 jobs)`.
- Install exit code 0 and a ready snapshot.

Cursor logged `Warming skipped (draft)`. This proves the native image and
install, but the draft was not the active Build used by new agents.

## Hardened retest

`scripts/setup.sh` now explicitly rejects a Build unless the Docker image marker,
the exact Verity revision, and solc `0.8.34+commit.80d5c536` are present. The
native retest Build ID, final status, and log evidence are appended after that
Build completes.

References:

- https://cursor.com/docs/cloud-agent/builds
- https://cursor.com/docs/cloud-agent/capabilities
