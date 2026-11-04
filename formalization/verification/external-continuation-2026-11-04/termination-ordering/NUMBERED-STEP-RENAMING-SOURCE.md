# Strict one-step forward typed renaming

Draft for review; no proof/export. Structural context prerequisite for paper 06 lines 583–597 and actual numbered reduction rules.

Both targets transport a single actual WindowStep/WindowArgumentStep through arbitrary typed renaming, including noninjective maps. Exact same symbols, S, precedence, types, labels and guards are used. The conclusion is one step, not equality-or-step. Renaming preserves non-bottom shape; the equality-collapse issue for general substitution does not apply to variable-valued environments. Forward transport does not require injectivity, finite-carrier or subtype closure.

Binder lifting is literal. Select retains selected occurrence and full argument suffix, Mul maps occurrence witnesses/nonempty removed list, Copy retains exact precedence/head guards, abstraction/opening and beta use accepted binding algebra. Only permitted contexts occur; no positive application-argument rule is introduced.

A proof may use a private stronger substitution helper for environments with non-bottom images, then specialize to variables and the accepted renaming presentation. It must not eliminate equality from the earlier general substitution theorem by assuming absence of self-steps.

No backward reflection, arbitrary-successor image closure, Acc/least-set/C stability, original-order transitivity or all-term/ID1 conclusion. Accepted files unchanged.
