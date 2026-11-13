# Second frozen original-certificate bridge

Read actual original source construction in
`UniformCertificateCompletion/OuterDefinitions.lean` and `Definitions.lean`:
`SourcePresentation.certificate` uses guarded positive paths over quotient
edges; their raw step first executes
`InternalOriginalUniformApplicationStepSelection.selectedChecker`, which is
the original `InternalParameterizedApplicationStepChecker.checkerP`.
The checked variable `closedIntroduction` stops at its old raw closed leaf.
No checked internal all-output nil-path checkerP equivalence was located.

`SelectedNilTargets.lean` freezes this exact intermediate bridge before proof
authorship. The original nil-path premise is the real certificate-left graph.
No replacement certificate, fuel, endpoint relation or runtime parameter is
introduced. Arbitrary old leaf outputs, including rejecting outputs, persist.

The second endpoint independently constructs the actual selected checker on
the original direct-variable certificate, discharging its raw old leaf through
the checked complete closed-wrapper constructor. This is an original source
step supplier; quotient normalization, positive-list packaging and full Object
source certificate erasure remain separate work. No completion claim for
paper06 `lem:id1` or all unrestricted source rules is made.
