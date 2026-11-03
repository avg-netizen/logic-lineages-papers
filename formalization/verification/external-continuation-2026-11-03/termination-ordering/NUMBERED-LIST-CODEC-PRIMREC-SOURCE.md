# Exact numeric-list primitive-recursion prerequisite

Paper 06, lines 551–556, calls the coded quotient relations arithmetic. This component does not establish that claim. It proves formal Mathlib Primrec facts for the already accepted natural ordered-list encoder and parser used by actual certificate codecs.

The finite first-order table has exactly bound+1 entries. Its initial entries are none; its next row uses literal unpair and earlier-row lookup. Calibration covers every value at most bound and every fuel, including zero. The predecessor lookup stays in range by the actual pairing inequality, not by a supplied oracle. Specializing bound=value recovers the existing value+1-fueled decoder exactly.

No accepted codec is changed. No full typed checker effectivity, arithmetic graph formula, unbounded search, relation decision, accessibility or well-foundedness is claimed. Existing formal-language program/defining-theory suppliers remain separate from pure arithmetic representability.
