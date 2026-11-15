# Original typeLists enumeration: exact3 frozen

Source: NumberedAuxiliaryEnumerationDefinitions.typeLists and its use in the
numbered branch of enumerate, also NumberedCodeEnumerationPrimrecSupportProof.layer.
Original typeLists S 0=[[]]; successor is [] :: S.flatMap (tau =>
previous.map (List.cons tau)). Preserve each occurrence, ordering, and duplicates.

The explicit AST operates on nested raw numeric lists: row constructs numeric
cons(typeCode,innerListCode), then keeps it as an outer entry. Outer cross appends
rows in S order; Nat recursion always prefixes empty-list code0. Base outer list
[0] is numeric1. No zero/None interpretation is used to filter output lists.

Native target uses the ACTUAL existing Encodable List Source.Ty and nested list
instances, not a custom replacement or assumed equality. Source.Ty has no n.
Proof must establish scalar type encode equals original typeNumber, recursive
list-code correspondence at both nesting levels, and all-raw decode totality
using the paid type-list decoder totality/canonicality. Raw list-Nat fold
calibration is an internal-to-native helper, not a replacement target.

Internal zero and successor concern actual graph observations only. The
successor law retains both actual prior recursion and cross outputs and pays
composition/recursion witnesses internally. No native reflection. This does not
complete internal enumeration membership/completeness, the full eight-constructor
code enumerator, classCodes/candidate Q installation, or paper06 accessibility.
Original codeBounds size/maxlabel remain unchanged; no nodeCount substitute.

No proof authoring before independent review and preflight release. Bounds
recurrence exact2 is native-passed and independent acceptance pending at freeze.
