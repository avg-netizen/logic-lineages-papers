# Native validation and portable scope

Four exact comparator aliases passed in `build-reports/1794157047016014438-5.json`.
All four new proof/audit namespaces have actual axiom-closure audits, totaling
17 declarations. Current component files have no warnings and use only
propext, Classical.choice and Quot.sound. Comparator-only preflight passed
before proof authorship in `build-reports/1794156856052596761-6.json`.
Independent postproof review remains pending.

`CLOSURE-SOURCE-PINS.json` pins 1,275 exact current local sources. The local
receipt map matches every source hash to a successful module row in an
immutable numeric receipt, with receipt and compiler-log hashes. All 110 used
receipts have the unchanged bounded serialized profile. All 1,051 broader
frozen Lean inputs also have successful native rows, and all 1,057 frozen/
input pins were checked unchanged. This is not a fresh aggregate rebuild.

The portable publication list contains the seven new Lean files, unchanged
frozen specification, source correspondence and pins, cumulative closure
source pins, status, acceptance, this validation and the exact-axiom log.
Numeric receipts/logs, full source-to-receipt maps, local summaries, failed
candidate snapshots, evidence collector and orchestration/release records
remain local evidence rather than portable proof dependencies.

Five checker sessions completed. The first internal candidate had a misspelled
supplier name; the first external candidate needed semantic-fold simplification
ordering and a dependent Decidable rewrite repair. Both failed source snapshots
remain local. The corrected current sources, final exact gate and all actual
axiom audits passed without changing any frozen comparator or accepted source.
Compiler admission was released at 16:57:53 UTC with both shared locks free.
No Git, global register, dependency, resource profile or CI file was changed.
