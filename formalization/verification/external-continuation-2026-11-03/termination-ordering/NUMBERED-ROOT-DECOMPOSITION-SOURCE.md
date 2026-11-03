# Exact root/context decomposition of the original guarded step

RootInstance contains exactly the actual non-context rules: the accepted four direct constructors, original Select, guarded Mul, and guarded Copy with the actual arbitrary precedence relation. Copy is not replaced by an assumed Boolean relation oracle. No context constructor appears in RootInstance.

Two targets are equivalences between actual WindowStep/WindowArgumentStep and one actual typed root instance plugged into the accepted one-hole context data. Both source and target must be literally the respective plugs. The hole binder context and type are existentially supplied by genuine mutual induction on the original reduction derivation, not assumed by a caller. The reverse implications must erase the root instance to a genuine step and use accepted context lifting. All actual constructors are covered, including argument tail occurrences and lambda context changes; no positive auxiliary application-argument context is added.

This decomposition has no endpoint Good or SubtypeClosed premise because it is structural, not a confinement theorem. It does not yet supply a recursive numeric parser/checker, prove executable certificate completeness, arithmetic representation or accessibility. The original local comparison and transitivity obstruction remain unchanged.
