# Theophysics Lean 4 Formalization

This repository is the reproducible Lean 4 capsule for the Theophysics formalization work.

The short version:

```bash
lake build
```

If Lean 4 is installed through `elan`, that command should download/use the pinned Lean toolchain and check the project from beginning to end.

## What is in this repo

The repo contains the Lean files needed to reproduce the current formal layer:

- `Final_Lean4_From_Excel.lean` - the original Excel-derived single-file spine.
- `Theophysics_Core.lean` - the positive theorem surface and integration marker.
- `Theophysics_Adversarial.lean` - negative tests, rejection theorems, false-positive guards, and boundary controls.
- `Theophysics_Coherence.lean` - coherence, order, passive entropy, active discoherence, and restoration gates.
- `Theophysics_Fracture.lean` - structured fracture/scar logic and repairability gates.
- `Theophysics_Fall.lean` - conservative Fall formalization: separation, coupling, entanglement, and grace-floor structure.
- `Theophysics_ChiEvaluator.lean` - deterministic skeleton of the chi evaluator: ten channels, product collapse, high-signal deception, pressure gradients, and Fruit output.
- `Theophysics_LawMechanisms.lean` - strong-law mechanism gates for Laws 1, 2, 9, and 10: domain failure, gate zero, and chi collapse.
- `Theophysics_MaxwellTrinity.lean` - finite Maxwell/Trinity shape gate: the quaternion case passes, six malformed alternatives fail.
- `Theophysics_DelayedChoice.lean` - finite delayed-choice quantum-eraser gate: erased/preserved coincidence subsets classify differently while the raw signal pattern remains invariant.
- `Theophysics_GodTest.lean` - finite God-marker gate pre-test: the full Christ-shaped marker passes; counterfeit death-victory candidates fail at least one required gate.

## First read

If you are not a Lean user, start with:

1. `PROOF_PACKET.md`
2. `WALKTHROUGH.md`
3. `REPRODUCIBILITY.md`
4. `INVENTORY.md`
5. `COVERAGE.md`

Then run:

```bash
lake build
```

## Current scope

This project verifies formal statements inside the definitions supplied in the Lean files. It does not ask Lean to verify every philosophical, theological, historical, or empirical claim surrounding the project. The important achievement here is narrower and stronger: the stated structures, gates, rejections, collapse rules, and adversarial controls compile in Lean 4 under the pinned toolchain.
