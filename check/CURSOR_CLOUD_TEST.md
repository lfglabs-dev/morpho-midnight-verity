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

No supported MCP or UI approval can promote a feature-ref draft directly.
Activation without modifying `master` requires a second, no-ref Build: use the
verified Docker Build snapshot as its base and have its install command fetch
the exact result-branch commit before running setup. A successful no-ref Build
is promotable and can be passed to `propose-environment-json`; Portal Save then
reuses the validated snapshot. The repository configuration and Dockerfile
remain the source of truth for the base snapshot.

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

### Final combined native Build

- Tested commit: `d078a0279b2edc6e5b92c68a4a4c6976268d10f5`
- Draft Build: `bld-20261002-b33eda78-ee99-4b41-bdb5-a576e6be2ac6`
- Build environment version: `2022036`
- Created/completed: `2026-10-02T14:17:07.720Z` /
  `2026-10-02T14:25:08.399Z`
- Status: **SUCCEEDED**

The complete native log records:

- Docker installation of `python3-venv` and `ripgrep`, Lean `4.31.0`, and the
  `/etc/morpho-proof-environment` marker.
- Verity revision `9b472a8a48a9990337845f1720a20f374fa1e9cd` and solc
  `Version: 0.8.34+commit.80d5c536.Linux.g++`.
- The reduced `Mathlib.Tactic` cache request (2,950 files rather than the
  previous 8,542-file full cache).
- Successful compilation of `Midnight.Import` and `Midnight.Spec` (38 jobs).
- Successful installation of all 43 version-pinned Python requirements and
  `lean-lsp-mcp 0.31.0`.
- Install exit code 0, snapshot ready, and terminal Build status `SUCCEEDED`.

A fresh Cloud validation run
`bc-c76c1fb7-b42c-50f6-bfa1-a471a6cdddca` cold-booted from this exact Build and
commit. It confirmed user `ubuntu`, the image marker, Lean/Lake/Python/ripgrep,
the exact Verity and solc pins, existing Import/Spec artifacts, a successful
38-job rebuild, and version `0.31.0` through both the binary and
`scripts/lean-mcp.sh`. Its working tree remained clean. It also independently
confirmed that no Lean/LSP MCP namespace is exposed without account/team MCP
registration.

This Build is fresh-run ready when selected explicitly by Build ID. It remains
a non-promotable feature-ref draft; the default-ref activation requirement in
the preceding section is unchanged.

## Doctor, startup, and real MCP smoke update

Input commit `ae85cc1` was integrated as `ae75778` while retaining all explicit
image, Verity, and solc assertions. It adds:

- `scripts/doctor.sh`, including `--require-image`;
- install-time and per-boot doctor checks;
- a real stdio MCP smoke test that requires zero errors for
  `Midnight/Spec.lean`, detects an intentionally broken temporary proof, and
  checks its exact Lean goal; and
- environment `start` readiness validation.

Static shell, Python, JSON, and current Cursor environment-schema checks passed.

### Promotable native Build and startup

The first no-ref activation candidate
`bld-20261002-bc194a73-da7b-466c-97d9-e862f7819c81` succeeded as environment
version `2022270`. Its native logs contain the complete doctor and real MCP
smoke output, and an exact-Build fresh run proved the automatic startup doctor
exited 0. Portal correctly refused to reuse it because its base snapshot came
from a separate Build context rather than this run's snapshot API.

The supported snapshot flow then completed:

- Local setup passed twice, including doctor and real MCP smoke.
- Snapshot `snapshot-20261002-e1087db7-943d-4359-a1bf-2d72d34c2693`
  reached `ready`.
- Final no-ref Build:
  `bld-20261002-91c2b8c1-a253-43db-a9d1-0b096a5ec6d1`
- Build environment version: `2022506`
- Created/completed: `2026-10-02T14:41:06.964Z` /
  `2026-10-02T14:45:03.871Z`
- Status: **SUCCEEDED**

The final native log proves checkout of exact commit
`a6e376e1fdaa06dfcd09b198b91b9c0cd924abaa`, all pinned tool checks,
`Midnight.Import`/`Midnight.Spec` compilation, doctor readiness, zero Spec
diagnostics, the intentional `unsolved goals` diagnostic, exact goal
`n + 0 = n`, install exit 0, and a ready snapshot.

Fresh run `bc-4239dce6-60c6-5cf1-b699-ddba174538d1` cold-booted from this exact
Build. Before manual commands, `/tmp/cursor/start-user/start-user.log` contained
`Morpho proof environment is ready.` and `start-user.status` contained `0`.
Manual doctor and MCP smoke also exited 0. The smoke emits a non-fatal Python
`BaseSubprocessTransport.__del__` warning after producing valid results.

`propose-environment-json` accepted this Build and the tested install/start
scripts. Activation now requires only **Save** in Cursor's Environment panel;
until Save, the environment still resolves to the original active Build.

References:

- https://cursor.com/docs/cloud-agent/builds
- https://cursor.com/docs/cloud-agent/capabilities

## Existing proof run and transport recovery

The environment conversation launched this proof run before the control-plane
transport interruption. Preserve it; do not launch a duplicate:

- Proof run: https://cursor.com/agents/bc-0a652130-5c98-50ca-b2c7-928e3ca00765
- Requested model: `gpt-5.6-sol-high` (actual model verification pending).
- Selected Build: `bld-20261002-91c2b8c1-a253-43db-a9d1-0b096a5ec6d1`.
- Proof-free input: `cursor/proof-sandbox@6ea1c1d`.
- Last reported state: running; no full theorem success is claimed.

Existing environment conversation:
https://cursor.com/agents/bc-b9f1d937-5f57-4610-9f29-b3ad5b47358b

Final cold-boot/startup/MCP validation:
https://cursor.com/agents/bc-4239dce6-60c6-5cf1-b699-ddba174538d1

Environment Save (if still pending):
https://cursor.com/dashboard/cloud-agents/environments/e/9e913d70-be66-11f1-bb68-864e54d14197

PR #2 remains draft and unmerged. The validated saved-snapshot route does not
require merging it; it is optional default-branch infrastructure. The earlier
merge-approval question is superseded by this supported snapshot route.

## Reattachment audit after deployment

A fresh read still reports execution revision 549 and the original final turn
`055f98b3-8c57-5ca6-9a1d-ab8b1309838b` /
`run-f8df1992-09ca-49f4-bcdf-74c88044bf1d` as `incompatible`.
No replacement test or cloud turn was launched. The existing proof result and
actual model remain unverified.

Read-only connector source inspection shows that unknown Cursor run statuses
map to `Incompatible`; the worker stops observing such turns and enqueue
rejects follow-ups until reconciliation. The actual triggering provider status
was not retained in this receipt, so its exact cause is not established.
The current MCP credential is executor-only and exposes no cloud reconciliation
operation. An operator must inspect the authoritative existing native run and
restore observation of that same identity through a supported recovery path.
Settling an action receipt alone does not establish that the cloud turn was
repaired. Failed follow-up action `f2ac9dad-4e51-459e-82cf-18a7d0c2a2bb`
remains `reconciliation_required`; do not replay it with another key.
