# Internal history preservation after iterator fusion

Status: source audit only. No new proof/specification acceptance is claimed.
The five checked November 13 history-fusion sources remain unchanged.

## Exact boundary

`SixSol20261112/HistoryMachine/NativeProgramsProof.nativePrograms` constructs
four Programs using `GorbowPRProgram.Proof.allPrimitiveFunctions`. Their
`KernelProgram`, `BoundProgram`, `InitialProgram`, and `FinishProgram`
contracts are all-vector *external* evaluation equalities. The outer iterator,
checker composition and fuel wrapper are syntax-explicit, which is why the
new internal iteration-fusion proof is valid without any native premise.
The kernel's actual history inspection and updates are not syntax-exposed by
those contracts. No internal history append/lookup/codec invariant was found
in the inspected Gorbow source family.

Consequently, a derivation about arbitrary symbolic histories cannot be
obtained merely by unfolding `KernelProgram` or applying its calibration.
The new fusion theorem does not supply append/reference preservation, and
neither does its same-source packaging.

## Next genuine supplier

The external source proof to internalize is
`GorbowTheoryCertificateOperationsProof.line_suffix`, followed by
`successfulHistoryExtension`. The first obligation retains arbitrary
runtime axiom-index/fuel, history h, history tail, and original line l:
acceptance of the original line on h implies acceptance of that same line on
h ++ tail. In rules 2 and 3, the exact references in the original payload
must first be proved less than the length of h, then the actual encoded
lookup at each reference must be proved unchanged by appending tail. Rules
0, 1 and 4 have history-independent tests but still require actual branch
and decoder equations. All malformed inputs must keep their original
rejection behavior.

Before freezing that internal formula, construct syntax-explicit Programs
for the *existing* Encodable History/List/Option codecs, original append,
length and optional lookup. Prove the symbolic lookup-under-append law in
ordinary source arithmetic, retaining the bound premise and all input terms.
Then construct a syntax-explicit original rule/line checker from those
Programs plus the existing non-history leaf tests. Rebuild the selected
history kernel and the one source tuple from that concrete syntax. The
internal line-suffix theorem must use the actual installed tags of this
construction, not an arbitrary program selected by external calibration.
No arbitrary source tuple already chosen from the old existential witness
can silently be replaced or granted new internal properties.

After line-suffix, a source arithmetic induction over the actual coded line
sequence can establish successful-history extension. Then the original
numeric MP construction requires exact result shape, history lengths and
references `antecedent.length` and zero. Full conditional HB2 additionally
retains rho in both inputs and its output. HB3 separately needs an internal
symbolic certificate-producer invariant; iterator fusion is not that proof.

No preflight was proposed for a generic theorem assuming these unpaid
suppliers, since that would not move this concrete checker past the current
boundary. The existing unchanged two fusion targets are the completed packet.
