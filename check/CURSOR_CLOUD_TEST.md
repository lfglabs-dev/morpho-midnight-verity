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
the exact Verity revision, and solc `0.8.34+commit.80d5c536` are present.

- Tested branch: `cursor/native-cursor-build-52c5`
- Tested commit: `4d3e9c76267edf1985d3742c6cc470cca3d05e4a`
- Draft Build: `bld-20261002-c0ec15b4-0aa1-4fa7-894d-6bc9d5f02235`
- Build environment version: `2021263`
- Source/trigger: `AGENT` / `MANUAL`
- Created/completed: `2026-10-02T14:07:04.559Z` /
  `2026-10-02T14:13:28.530Z`
- Status: **SUCCEEDED**

The complete native log confirms:

- Docker build started at `14:07:33Z`, used `.cursor/Dockerfile`, materialized
  `/etc/morpho-proof-environment`, and exited 0.
- The install printed Lean `4.31.0` and Lake `5.0.0`.
- Verity checked out at
  `9b472a8a48a9990337845f1720a20f374fa1e9cd`; the new exact-revision assertion
  passed.
- The checksum-pinned installer installed solc
  `0.8.34+commit.80d5c536`, and the new executable-version assertion printed
  `Version: 0.8.34+commit.80d5c536.Linux.g++`.
- `Midnight.Import` and `Midnight.Spec` compiled, all 38 jobs completed, and
  the install exited 0.
- The snapshot became ready at `14:13:26Z`; Cursor's terminal Build status is
  `SUCCEEDED`.

## Activation

Cursor explicitly reports that a draft Build created from a non-default ref can
be tested but cannot be promoted to active. It logged `Warming skipped (draft)`.
The active Build for the current environment therefore remains the initial
default-image Build `bld-20261002-a309b12f-e20a-4989-8968-d2781a34df2f`.

No supported MCP or UI approval can promote this feature-ref draft directly.
Without editing `master` in place, activation requires merging the environment
commit, then allowing or triggering a Build with the repository default ref.
That successful default-ref Build becomes active and is the Build from which a
fresh proof agent should be launched.

`propose-environment-json` was not used: its supported proposal fields are only
`install` and `start`, so it cannot preserve this environment's Dockerfile
base. The repository configuration and Dockerfile remain the source of truth.

## Lean MCP environment update

The infrastructure update from input commit `2e84d22` was integrated as
`5c280f2` without removing the Docker marker, Verity revision, or solc version
assertions added above. The resulting configuration:

- installs `python3-venv` and `ripgrep` in the Docker image;
- runs Build installation explicitly as user `ubuntu`;
- warms `Mathlib.Tactic` instead of the entire Mathlib cache;
- installs `lean-lsp-mcp==0.31.0` and 42 transitively version-pinned
  dependencies into `.lake/lean-mcp`;
- exposes `scripts/lean-mcp.sh` as the repository-local stdio launcher; and
- keeps `.cursor/mcp.json` for Cursor IDE configuration.

The built-in Cloud tool catalog for this run contains no Lean or LSP MCP
namespace. A repository `.cursor/mcp.json` does not register a Cloud Agent MCP.
To expose Lean MCP tools in a fresh Cloud run, add and enable a custom **stdio**
MCP in personal or team Cloud MCP settings with:

- command: `sh`
- argument: the checked-out repository's absolute `scripts/lean-mcp.sh` path
  (for a single-repository `/workspace` checkout, `/workspace/scripts/lean-mcp.sh`)

The native Build verifies that the pinned server installs and starts far enough
to print its version. A real `lean_diagnostic_messages` call still requires that
account/team MCP registration and a fresh Cloud run.

The final native Build evidence for this combined configuration follows after
the branch-ref Build completes.

References:

- https://cursor.com/docs/cloud-agent/builds
- https://cursor.com/docs/cloud-agent/capabilities
