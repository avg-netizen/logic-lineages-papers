# Zero constructor qualification correction

Approved proposed sole replacement of the two target occurrences OriginalTerm.zeroC with (.zeroC : OriginalTerm Γ .ground). Compared current target with preserved failed edition: byte-identical. Read preserved log receipt 1795020178067952931-5: both failures are precisely the unknown abbreviation-qualified constructor. Actual SourceTerms.lean declares Term.zeroC with the required context/ground type.

This restores the literal constructor intended in the approved ZeroCalibration target; no body, domain or mathematical value changes. Preserve original source/freeze/receipt; update only the target hash, then request independent applied-diff/hash confirmation before a fresh native ticket.
