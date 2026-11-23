# Paper 16: include zero in the full canonical finite coefficient carrier

This is a reindexing of the already checked actual variable-dimension
band image under each fixed original closed tower `t_(l+2)`, not an
additional physical point. The displayed structural carrier consists of
the empty word (zero) or a finite big-endian list with positive leading
coefficient. The exact strict order first compares list lengths, then
ordinary dictionary order at equal length.

* `NativeTowerBandFullCoefficientModelProof`: send the empty word to the
  old word `[1]`; send a positive singleton `[a]` to `[a+1]`; leave all
  longer words literally unchanged. The explicit inverse deletes `[1]`,
  decrements any other singleton, and leaves longer words untouched.
  Proves both round trips, exact comparison in both directions, and the
  three literal mapping equations. In particular `[0]` is still excluded.
* `NativeTowerBandFullCoefficientRelIsoProof`: the explicit maps yield
  a relation isomorphism onto the checked positive words, and composition
  yields a relation isomorphism onto exactly the original native subtype
  `BandImage S l`. The empty word denotes the physical first band point
  `bandImage S l ⟨0,0⟩`, not the original literal closed term Z. Every
  native image term still lies strictly below the same `closedTower S
  (l+2)`. The model inherits the checked well-order of that image.

The original witness source remains the actual terms in Paper 16
`ordinals.tex`, constructions (B_T) and (D); this is a model of the
existing band coordinates, not a new implementation of those terms.
No named ordinal interpretation, rank, cofinality, or height is claimed.
The first gate uses the already checked core coefficient closure. The
second uses the already checked relation-isomorphism closure. No Ordinal
module, new cache, or limit changes are required.
