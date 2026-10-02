# Cursor Cloud proof-generation test

Status: launched; Docker provisioning and theorem verification are not yet certified.

- Input branch: `cursor/proof-sandbox` (proof-free).
- Initial input commit: `b770ed1f65fddb705c489486a54b0f2650a03806`.
- Verifier hardening: `ba7c2d0` (requested on the cloud result branch).
- Provider/account: `cursor_cloud` / `cursor-default`.
- Requested model: `gpt-5.6-sol`, 1M context, reasoning max, fast false.
- Mission: `9701ccc9-e635-47dc-90eb-86ce764e7d6c`.
- Cursor: https://cursor.com/agents/bc-9701ccc9-e635-47dc-90eb-86ce764e7d6c
- Result branch: `cursor/midnight-proof-cloud-validation-363f`.

Acceptance requires actual Docker build/provisioning evidence, Lean diagnostics,
a proof of the unchanged `Midnight.Spec.updatePositionViewProperties`, and a
passing exact-type/axiom audit. The generated proof belongs on the result branch;
the input branch must remain proof-free.

The connector currently exposes running/queued state but no readable command
transcript or result. A running status is not evidence that the Dockerfile or
proof succeeds. The local orchestration workspace has a Docker CLI but cannot
access its daemon, so no local Docker success is claimed.

Cursor's setup documentation says Builds use default-branch configuration, and
feature branches can reuse the active Build. Check `/etc/morpho-proof-environment`
first; if absent, explicitly build and run the supplied Dockerfile in Cursor.
Distinguish that explicit test from automatic environment selection.

Reference: https://cursor.com/docs/cloud-agent/setup
