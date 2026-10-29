# The exact computability of two adversarial prediction measures

[Paper (PDF)](paper.pdf) · [Canonical TeX](paper.tex) · [Sources](SOURCES.md) · [Verification](VERIFICATION.md)

Hibbard's original measure and its strict comparator have exact oracle degree **0'''** on total binary predictor indices in the stated ordinary machine model. Sufficiently high fixed thresholds and the infinite-value predicate are Π⁰₃-complete. The canonical repetition-free list of all total computable functions gives a second measure of the same degree, although every value of that measure is finite.

This eight-page paper combines the original-measure classification with the specified all-total-function variant. It includes the recursive-matrix upper bound, a baseline robust to modified predictions, complete hardness reductions, the canonical-list construction and exact jump accounting. It addresses a specified instance of Alexander–Hibbard's conjectured oracle increase, while leaving arbitrary reorders and other taxonomies open.

Totality is a promise on input indices. Runtime is worst case over every input of a given length, and the input-tape convention permits reading a bounded prefix without scanning the entire input. The canonical list's bound programs are ordinary programs even though selecting their indices requires 0''.

Build with `python3 build_pdf.py` here; cached Tectonic resources or pdfLaTeX suffice. `--online` permits missing resources on a new Tectonic installation. All macros and the Computer Modern preamble are local.

AI-assisted hand-proof manuscript for review, without formal certification or an established priority claim.
