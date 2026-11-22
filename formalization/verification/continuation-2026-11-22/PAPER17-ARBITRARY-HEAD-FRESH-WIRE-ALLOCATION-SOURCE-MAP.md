# Fresh hidden wires for the original arbitrary fixed-head gate list

Paper 17, `17-permitted-control-canonical-comparison/sections/arithmetic.tex`, lines 3–27 and 33–48. This removes precisely the caller-supplied hidden-name premise of the accepted #978 original arbitrary-head wire list.

- Start at one beyond the exact maximum of all original source/output names (empty default zero). Allocate successive numerical candidates in original occurrence order. A finite-head gate never allocates its candidate in the hidden namespace.
- The original ordered list is reproduced exactly by dropping candidate names. Every actual hidden name is strictly above the maximum of all original wires, and all such names are distinct. This holds for arbitrary finite lists and repeated original names, with no fresh-name hypothesis.
- Apply the exact #978 normalized/raw conjunction equivalence to the literal original list. The hidden extension is unique precisely on the original raw conjunction and leaves every coordinate at or below the original maximum unchanged, even coordinates that are not mentioned in the list. It also agrees outside all actual hidden names as in #978.
- No original output discovery, broader topological circuit or DAG parser, encoding/effectivity theorem for this representation, computed low cutoff, or arithmetic decision is asserted.
