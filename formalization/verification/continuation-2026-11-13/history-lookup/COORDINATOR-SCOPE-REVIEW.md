# Coordinator source-scope review

Reviewed frozen Definitions/Targets and actual LookupProof/ReferenceProof after exact6 native PASS1794566262907984480-31. No concrete scope defect found.

The actual lookup composes repeated-tail drop with a literal zero/nonzero reference branch. The reference uses zero for none and successor(headCode) for some, so an entry whose code is zero is not confused with failure. Internal zero-cons follows the actual drop-zero and reference-cons equations; successor-cons follows the internally derived drop-cons equation; all-index nil follows drop-nil and reference-zero. Cross-tag head/tail cons inputs retain actual registry installation premises. No native evaluation theorem is reflected into these internal derivations.

Native history calibration is separate and matches original History.getElem? encoding. These equations do not yet establish arbitrary valid-reference append preservation, full checker rule correctness, history fusion soundness or HB2/HB3. Native evidence status is reported separately.
