# Actual WindowStep preserves binder-aware support forward

Draft for review; no proof/export. Actual auxiliary rule support supplier for paper 06 finite-context reasoning.

Both targets are one-way support preservation under the literal WindowStep/WindowArgumentStep, for arbitrary typed P. No precedence, finite-window closure or injectivity assumption is added. Reverse fails for unsupported variable→bottom.

All constructors: Put retains base and empty extras. Select takes the selected actual occurrence from base++extras using list calibration, and supported selfArguments/applyArguments handle the complete suffix. Copy uses the same self-copy supplier. Mul uses the original kept/removed/inserted witness and forward PrimitiveMultiset support; no reverse or nonempty-inserted claim. Abs uses openNumbered under lift P. Recursive ordinary/numbered argument, function and lambda contexts use the appropriate IH, with lift P under lambda. Beta uses predicate-respecting substitution from lift P to P: here maps to the supported argument, there to the corresponding variable. Bottom has trivial support. No positive application-argument rule is introduced.

Primary support is separately accepted. Image closure, quotient reflection, Acc/C stability, all-term or ID1 conclusions are not these targets. Prior accepted bytes unchanged.
