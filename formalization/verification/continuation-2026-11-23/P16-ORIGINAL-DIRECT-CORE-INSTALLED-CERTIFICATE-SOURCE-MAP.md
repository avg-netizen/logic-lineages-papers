# Paper 16: installed original odd certificate to one actual shared tape

Source freeze, pending exact native gate. Paper 16 `sections/ordinals.tex:84–98`
puts the multiset replacement in the odd tagged (A) clause, and
`NumberedWindowDirectAlgorithm.lean:12–38` fixes source, certificate and
target order and the tag-5 ordered witness fields.

`ExactInstalledCertificateSharedTape` takes a derivation of the actual odd
`certificate S true c src dst w`, under the literal `sourceBody S c` for
`S := data i j r (dCore i r count)`, the same choice made by #1523–1524. It
does not assume the raw acceptance or parser reports. `exact_CertificateRules`
projects original syntax `[context,src,dst,w]` into exactly the physical
`[src,w,dst]`; no fields/tapes are changed. The accepted #1515 theorem
uses that same raw positive graph to choose the one shared ordered tape and
supplies actual tag-5 packed equality and raw field reports, physical scalar
and removal boundary, exact two partition callbacks, and actual insertion
scan in the corresponding strengthened object context. Same (c), formula,
and consequent derivation context throughout.

This is a graph-only elimination for any concrete supplied observer. Even
numerical `CountFit` is not used in the elimination; it remains required for
the separate #1523/#1524 numerical/semantic interpretation install. Does not
establish any count observer exists, its internal frequency semantics, any
new successor theorem, arbitrary J, or old/new body equality.

| Module | SHA-256 | Source local closure |
|---|---|---|
| `NumberedWindowInternalDirectCoreInstalledCertificateTargets` | `bb61127af148a736287756008ff035a6c7b7fdd9ca4577e7bb7cf8ca05d415ff` | 1113 |
| `NumberedWindowInternalDirectCoreInstalledCertificateProof` | `cb15f003f0c0e8f3858ca7f98807239c46705b9d975ee63197608c91232e406c` | 1281 |
| `NumberedWindowInternalCoordinateChecks` | `d02d0f021bc269e7e845ad799c723fd29e32448a4e8c08f29210ba47eadad44c` | existing |
| `NumberedWindowInternalDirectCoreSharedTapeChecks` | `477ad3a4ddee18e2d06b0c6b4f56d472ab8484f47a85f5979bb2b5f684ace31f` | existing #1515 |

Source scan reports 32 external imports, with no Hydra, GameAdd, Sym2, or
Linarith in the closure. Exact gate:
`NumberedWindowInternalDirectCoreInstalledCertificateProof.exact_InstalledCertificateSharedTape`.
