# kusnerl1

Lean formalization of Kusner’s conjecture in dimensions five and six:

```lean
KusnerL1.equilateralDimension_five : KusnerL1.equilateralDimension 5 = 10
KusnerL1.equilateralDimension_six  : KusnerL1.equilateralDimension 6 = 12
```

See [`KusnerL1/Main.lean`](KusnerL1/Main.lean) for the main theorems.
A link to the preprint will be added when it is posted. The formalization
predates later revisions and will be updated and reverified for the final paper.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

Lean 4.33.1 and all dependencies are pinned. The build includes
[`Audit.lean`](Audit.lean), which prints theorem statements and axiom dependencies.
The latest local build passed without warnings; all 63 audited declarations
use only `propext`, `Classical.choice`, and `Quot.sound`.

## License

Copyright © 2026 Drew Gallinger. Code, documentation, and configuration are
[Apache-2.0](LICENSE). Dependencies retain their respective licenses.
