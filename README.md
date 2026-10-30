# Educational Isabelle/HOL Model of Zircon-Style Capability Transfer

## Overview

This repository contains an **educational** formal model of a Zircon-inspired
capability-transfer fragment in Isabelle/HOL. It is **not** a complete
verification of the Zircon microkernel, of Fuchsia's TCB, or of the full
syscall surface.

The model covers processes with handle tables, channels as kernel objects
(accessed via endpoint handles), rights reduction and **move** semantics on
`zx_channel_write`, and VMO write permission checks, with machine-checked
proofs of the corresponding security properties.

Companion article (Russian): `blog/zircon-capabilities-blog.tex`.

## Tool versions (reproducibility)

| Tool | Version used |
|------|----------------|
| Isabelle/HOL | **Isabelle2025** |
| OCaml | **4.14.1** |
| zarith (via ocamlfind) | **1.14** |

## Key Features

### Formal Model

- Per-process handle tables and monotonic handle-id allocation
- Channel objects with capability queues (`create_channel_pair`)
- Endpoint access gated by `ZX_RIGHT_WRITE` / `ZX_RIGHT_READ` on channel handles
- Move-into-message: successful write clears the sender's payload handle
- VMO content store for integrity examples
- Operations: `create_channel_pair`, `create_vmo`, `zx_channel_write`
  (move + `reduce_rights_wf`), `zx_channel_read`, `transfer_via_channel`,
  `vmo_write`, `zx_handle_duplicate`, `zx_handle_close`
- Trace layer (`Zircon_Traces.thy`): `reachable`, `state_wf`,
  `reachable_preserves_wf`
- MMIO bypass (`Zircon_MMIO.thy`): `privileged_vmo_poke`,
  `mmio_leak_witness_true`, store-isolation counterexample
- Portable locale (`Portable_Capability.thy`): monotone attenuation +
  optional dependency closure

### Verified Properties

- **No rights escalation** (`channel_transfer_no_escalation`) for the
  composition `transfer_via_channel` (successful write then read)
- **Object preservation** (`transfer_via_channel_preserves_object`)
- **TRANSFER / channel-WRITE gates** (`channel_write_requires_transfer`,
  `channel_write_requires_channel_write_right`, …)
- **Move** (`channel_write_moves_sender_handle`,
  `transfer_via_channel_moves_sender` for `src ≠ dst`)
- **Data integrity** (`vmo_write_denied_without_write_right`, …)
- **Example** (`example_scenario_true`): channel pair, VMO with
  READ|WRITE|TRANSFER, transfer only READ; sender handle gone; B's
  `vmo_write` fails
- **Empty rights** (`example_empty_rights_ok_true`): transfer with
  request `{}` yields an empty-mask handle; integrity still holds
- **Lattice view** (`Zircon_Lattice.thy`): `reduce_rights = inf`;
  `combine_rights = sup`; dependent rights via `rights_wf` /
  `reduce_rights_wf`
- **Traces**: `reachable_transfer_no_escalation`,
  `reachable_duplicate_no_escalation` (premise `rights_wf` from `state_wf`)

Rights on the syscall path use closed intersection:

```
actual_rights = close_rights (req_rights ∩ src_rights)   (* reduce_rights_wf *)
```

## Build

```bash
isabelle build -d . Zircon
```

Requires **Isabelle2025**. PDF output is written under `output/` when
document generation is enabled in `ROOT` (`output/` is gitignored; rebuild
locally). Theory `Zircon_Code.thy` (document disabled) exports OCaml to
`generated/Zircon.ml` and runs `test_code "example_exec_ok" in OCaml`.

### Extracted OCaml

```bash
cd generated && make test   # ocamlfind + zarith 1.14 (OCaml 4.14.x)
```

Expected: `PASS: example_exec_ok = true` (and the empty-rights line if present).

## Model Limitations

- Simplified identifiers (`nat`), not full 32-bit handle encoding
- No concurrency; incomplete syscall / object API
- **`transfer_via_channel` requires an empty destination channel queue**
  (real Zircon `zx_channel_write` may enqueue into a non-empty queue;
  the main no-escalation theorem is stated for this composition)
- Object-creation policy (who may mint which rights) is out of scope
- Incomplete rights set relative to real Zircon; pedagogical
  `WRITE`/`EXECUTE` ⇒ `READ` dependency (real Zircon bits are independent)
- `portable_capability` covers monotone mask attenuation (+ optional
  dependency closure) only — not ACL/DAC, RBAC, IFC, or full seL4 CSpace

## Theories

| Theory | Role |
|--------|------|
| `Portable_Capability.thy` | Locale for portable attenuation interface |
| `Zircon.thy` | Ontology, syscalls, core lemmas |
| `Zircon_Lattice.thy` | Lattice view + locale interpretation |
| `Zircon_Traces.thy` | Reachability, `state_wf`, transfer no-escalation on traces |
| `Zircon_MMIO.thy` | Negative witness (privileged poke) |
| `Zircon_Code.thy` | OCaml extraction / `test_code` (`document = false`) |

`Zircon_Attacks.thy` is an **optional internal** test theory (`document = false`);
it is **not** cited in the article and is not part of the educational narrative.

## Related Work

- Formal Methods for OS Kernels: seL4, Verve, CertiKOS
- Capability-Based Security: Levy, Capability-Based Computer Systems
- Zircon/Fuchsia documentation: https://fuchsia.dev/fuchsia-src/concepts/kernel
- Isabelle/HOL: https://isabelle.in.tum.de/

## Authors

- redbeardster
