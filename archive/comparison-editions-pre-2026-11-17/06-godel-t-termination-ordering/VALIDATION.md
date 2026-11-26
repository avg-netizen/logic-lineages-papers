# Document validation

The canonical source was compiled with `python3 build_pdf.py`, using
Tectonic with `--untrusted --keep-logs --only-cached`. The resulting PDF has
**14 A4 pages**. Its text and mathematical fonts are embedded Computer
Modern/AMS families (with the compatible standard TeX text symbol font where
used); the exact font table is in `document-checks.json`.

Checks completed:

- Every local TeX input and every referenced companion PDF is present.
- All citation keys and cross-reference labels resolve; labels are unique.
- The final TeX log has no undefined-reference or overfull-box warning.
- The mathematical body has no TODO markers or private proof-source paths.
- Public source records contain descriptive titles and hashes, without
  inaccessible workspace paths or private project labels.
- PDF text extraction completed with no unresolved-reference question marks.
- Representative title and technical pages were rendered and inspected for
  margins, formula placement and readable Computer Modern typography.

The source contains 6 theorem, 17 lemma,
1 corollary and 1 example environments.
The argument is a mathematical hand proof. Compilation and document lint do
not certify its correctness; no Lean artifact, independent reviewer judgment
or feasible implementation is asserted. No giant standard-control value was
evaluated. `PROVENANCE.json` identifies consolidation inputs separately
from reader-facing published and included-companion references.
