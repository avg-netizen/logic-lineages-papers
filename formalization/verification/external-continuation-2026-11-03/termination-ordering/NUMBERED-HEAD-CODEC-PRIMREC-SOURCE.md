# Exact finite-signature head-code primitive recursion

Paper06 lines551–556 requires effectivity of actual coded syntax before arithmetic quotient claims. This component concerns the existing six-tag HeadCode codec only. Its honest finite-sum presentation preserves both nullary heads, both single-type heads, the ordered pair of application types, and every Fin n ranked identity.

Targets quantify every fixed n, including zero, and establish formal Primrec of actual headNumber, headParse n and decodeHeadNumber n. Invalid tags, nonzero payloads for nullary tags, and out-of-range ranked payloads retain their actual failure behavior. The existing validation filter is part of the target, not deleted or assumed sound. Type payloads use the already accepted exact type codec.

No recursive Code or typed Packed decoder effectivity, full checker effectivity, uniform signature encoding, arithmetic representability or well-foundedness is claimed. Accepted implementations remain immutable.
