# Independent primitive-recursive restricted syntax checker

Target-only proposal for the decidable source-class prerequisite to paper09 hardness.tex lines311–319. The existing independent RestrictedSyntax is unchanged; this checker is not an image test for the generated reduction.

FragmentCode follows the exact existing source tags: variable0, canonical zero1/successor2, application5, lambda6 with ground domain code. Case3/recursor4/tag7 are rejected; noncanonical payloads on tags1/2 are rejected. Variable indices are not validated by fragmentCode alone. GroundCode separately invokes the accepted exact source type checker in replicate n ground. RestrictedCode decodes the existing (n,left,right) tuple and conjoins both ground checks and fragment checks; failed tuple decoding returns false.

FragmentCalibration is for actual typed syntax. ExactSyntaxClass uses actual typedCheckExact witnesses and the already proved AllGround+Fragment internal-level theorem, rather than assuming a numeric type-support bound or changing the source class. UniformPrimitiveRecursive covers all raw inputs; MalformedCases states the explicit rejected cases.

No valuation coverage, counterexample search, source-language upper bound/completeness, weak comparison, complexity or publication claim. Existing syntax, independent semantic language and register remain unchanged.
