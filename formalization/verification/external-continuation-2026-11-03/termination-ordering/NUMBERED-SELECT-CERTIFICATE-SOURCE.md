# Exact typed Select occurrence and complete-suffix certificates

A certificate consists of an actual occurrence index in the concatenation of the source base list and extras, together with the complete ordered list of argument types. The checker accepts only a successor-numbered source. It reads the exact selected packed occurrence, checks its type equals arrows types sourceResult, and applies the actual selected term once through the complete existing applyArguments operation to the entire selfArguments list built at the predecessor label from the original full source base/extras. Empty type lists are included. There is no iterated unary replacement of the source rule, deletion of extras or loss of multiplicities.

SelectInstance is precisely the original Select constructor with actual list membership. The first target proves existence of executable certificates exactly equivalent to that constructor; membership-to-index witnesses must be derived. The second proves actual WindowStep and target confinement from initial InUniverse under explicit SubtypeClosed, without assuming selected or target confinement separately. Typed transport is the equality checked by the executable branch.

Recursive contexts, certificate numeric encoding, complete rule checking and arithmetic representation are separate. No original ordering rule or transitivity obstruction is changed.
