# Understanding Why It Had to Be Done Is What Unique Games Is About

**Author:** José Luis López Rangel  
**ORCID:** 0009-0007-8566-4218  
**Version:** 0.3 (English edition)

This deposit presents an independent exposition and formal audit of the information-transfer architecture in OpenAI's *The Unique Games Theorem*. Its purpose is to support mathematical understanding and careful inspection of the original proof. It does not claim a new proof of the Unique Games Conjecture or an error in the original proof.

## Files

| File | Purpose |
| --- | --- |
| `Unique_Games_v0.3_EN_publication.pdf` | Main manuscript. |
| `LeanJuegosUnicos.lean` | Standalone Lean audit. |
| `compilacion.log` | Full output of the Lean compilation and axiom queries. |
| `README.md` | Scope, reproduction steps, and rights. |

## Scope of the Lean audit

`LeanJuegosUnicos.lean` uses exact rational arithmetic and finite distributions defined in the file itself. It has no imports from Mathlib or OpenAI's Lean library. It verifies algebraic identities, scaling relations, finite negative controls, a coupled projection regime, and the conditional mass-flow closure. The final theorem takes the local lower bound, pointwise equality of laws, clean-coordinate upper bound, and strict separation as fields of `SoundnessAuditBundle`. This deposit does not derive those four fields from OpenAI's original formalization.

## Reproduce the check

Use Lean 4.34.1. From the directory containing the four files, run:

```sh
lean LeanJuegosUnicos.lean
```

The command should exit with code 0. It prints the transitive axioms for 17 selected declarations; the included `compilacion.log` records `[propext, Quot.sound]` for each and no `sorryAx`.

## License and permitted use

Copyright © 2026 José Luis López Rangel. **All four files are licensed under [Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International (CC BY-NC-ND 4.0)](https://creativecommons.org/licenses/by-nc-nd/4.0/).**

You may download, cite, and share the files unchanged for noncommercial purposes with attribution. You may execute the unmodified `LeanJuegosUnicos.lean` for noncommercial verification. Redistribution of modified versions and commercial use require the author's prior written permission. The license does not restrict uses otherwise permitted by applicable law.

For citation, use the Zenodo DOI assigned to this deposit together with the author's name and the manuscript title.

## Source under study

OpenAI, [*The Unique Games Theorem*](https://github.com/openai/math/blob/main/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf), 2026.
