# Primitive-recursive original auxiliary syntax measurements

Paper06 lines551–556 uses the finite computability of primary classes while
preserving labels, types, and extra-list order. The existing `classCodes`
implementation enumerates with the original term's maximum finite label,
structural size as tuple bound, and twice that size as depth bound. Effectivity
of that exact implementation therefore requires these original measurements.

`codeBounds` is a total structural function on the existing `Code Symbol` with
output `(size, maximum finite label)`. Variables and bottoms have size one and
label zero. A lambda or ordinary head adds one to its child's size. An application
adds one to the ordered sum of its two child sizes. A numbered head adds one to
the sum of its base and extra sizes and takes the maximum of its own finite label
and both child maxima. An empty argument list has size and label zero. An
argument cons adds the two child sizes without counting the list constructor and
takes the maximum child label. Thus its size agrees with the original term and
argument measurements, which differ from the separate request evaluator's Code
node weight.

The first two frozen targets identify these pairs exactly with
`(NumberedPrimaryEquivalence.size, maxLabel)` on every actual term code and with
`(NumberedPrimaryEquivalence.argumentsSize, argumentsMaxLabel)` on every actual
argument code. These calibrations quantify over arbitrary symbol types and
arities, contexts, result types, and argument-type lists. The third target proves
`codeBounds` primitive recursive on all codes over every finite signature,
including malformed typed inputs and the empty signature. The fourth target
proves the pair of original measurements primitive recursive on the existing
packed typed syntax under its accepted numeric presentation. No window,
subtype-closure, membership, or effectivity hypothesis is introduced.

The planned code proof uses Mathlib's `Primrec.nat_omega_rec'`: the rank is the
accepted primitive-recursive `codeNumber`, dependencies are the literal immediate
recursive Code children, and strict rank descent follows from the actual nested
pairing formula. A primitive-recursive one-layer constructor algebra combines
the child results. The final packed theorem composes this result with the exact
original `packedCode` projection and the term calibration. Both effectivity
suppliers must be proved as actual functions rather than postulated as premises.

This component supplies the exact measurements consumed by the original finite
syntax enumeration. Class enumeration, decoded candidate lists, exchange testing,
primary classes, least representatives, canonical carrier effectivity, and whole
paper06 arithmetic or accessibility claims require their remaining dependencies.
The source-statement register remains unchanged.

## Prospective statement freeze

The following hashes were recorded before candidate proof authoring. Comparator
compilation and acceptance evidence belong to separate integration records.

| Source | SHA-256 |
|---|---|
| `NumberedPrimaryEquivalenceDefinitions.lean` | `de83b3654dee5eee9b73afa035fb1660fce2e787709c47c13cfe23b587448f50` |
| `NumberedAuxiliaryCodingDefinitions.lean` | `88fb4093b2e7dd8879bfd5edc8f5234f610e3085dcf87bb27bced4ff47a816a5` |
| `NumberedAuxiliaryEnumerationDefinitions.lean` | `7d72fed1e2094ef5131dd4a00697925817841c95ff833654c4ec2e25b305c2ff` |
| `NumberedLeastCodeRepresentativeDefinitions.lean` | `e35aa2dc92dfa7862cfec6dfa1fd90352d2d673079893b9763030d0eec3dda22` |
| `NumberedPackedPresentationDefinitions.lean` | `2b9dd41c24b02c84eecd2d802390706ad94cc6dd39bb5a9c356c21ab1065d266` |
| `NumberedCodePresentationDefinitions.lean` | `b5834668c429b5769be797857f151bb08648a23449a98a5e0ab680f7ac2f5cd4` |
| `NumberedSyntaxBoundsPrimrecDefinitions.lean` | `9e433342262f28c502383740b8fc303836d67c520ff1a20f6c5e78b18dae0d17` |
| `NumberedSyntaxBoundsPrimrecTargets.lean` | `4ec91ca24edd59a5bf5f7473af953e0b9945bac40ea02b6d6bf0560bff20ff16` |
| `06-godel-t-termination-ordering/paper.tex` | `bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e` |

## Accepted verification

The fixed statement gate and the sixteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](CLASS-CANDIDATES-FREEZE.json) and
[the acceptance record](CLASS-CANDIDATES-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
