# Exact same-context argument-domain bridge

Baseline: `2aee992743f72cd3163c79c9340c6012a3ea1904`. Paper06
`paper.tex` lines 570–588 uses arbitrary computable arguments within the
ambient typing context. A uniform object-code formula must not accidentally
quantify arguments in other Gamma fibers. This component supplies that
arithmetic domain bridge, not the C_tau construction or its induction proof.

The codec target explicitly concerns the EXISTING ContextUniform.Object and
its existing Encodable instance. Generic Encodable.decode does not imply
encode-after-decode. Here Ty uses the existing Primcodable.ofEquiv Nat
typeEquiv instance; the standard List and product encodings agree with their
denumerable encodings. The proof must establish exact original decoder
inversion, totality and equality with decode2, without replacing the original
instance or silently substituting decode2 in any existing checker.

The same-context guard uses the ORIGINAL two Object decoders and equality
of their decoded Gamma fields. Its actual Program 2 is compiled by the
existing SourcePresentation.checkerFormula. All natural inputs are covered.
The existing rejection branches are retained; codec totality is proved for
these Object codes only, not for universe/payload/context decoders.

The domain target states that the guard against objectCode Gamma x accepts
EXACTLY objectCode Gamma a for some payload a. Universal and existential
quantifier equivalences hold for every arbitrary predicate Q, so no foreign
Gamma assumptions or closure hypotheses are introduced. The typed version
uses the ORIGINAL typed-carrier predicate through its accepted exact fiber
calibration. No normalized replacement operator, changed numbering or
strengthened source carrier is used.

Nonduplication: ContextUniformFiberProof only calibrates the four original
relation/carrier fibers; JointGammaApplication covers same-context graph
instances, not argument-domain quantification or exact Object codec inversion.
No accepted arithmetic same-context guard, decode/decode2 bridge or uniform
argument quantifier theorem was found. Existing generic Denumerable facts
are suppliers only after matching the actual concrete codec.

Definitions/targets and original codec/semantic hashes are frozen before
proofs. Exact aliases, source matching and standard-axiom audits use unchanged
serialized caps. No existing source/target, manuscript, register, checker,
dependency, root import or CI change. No C_tau computability, internal ID1
derivability, accessibility, well-foundedness, whole lem:id1 or II5 claim.
