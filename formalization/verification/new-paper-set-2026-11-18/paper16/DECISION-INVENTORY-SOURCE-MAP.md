# Decision inventory exact scope

Source: decision.tex opening paragraphs and the universe bookkeeping underlying finite closure. This is a preliminary supporting packet, not lem:observation-closure.

`inventory` computes K, V, the literal source-head inventory and B directly as finite lists/natural depth. Membership permits duplicate occurrences. `freeInventory` is compared to the previously checked typed free-occurrence predicate. `LambdaPath` traverses actual base/extra subterms; its bound and attainment certify the maximum, not an arbitrary chosen budget.

The separate auxiliary support includes each original head declaration (result and each uncurried argument type), current marked output, and all base/extra support. It never replaces the existing literal ordinary support. The exact ordinary correspondence has actual `Typed Γ q τ` and `Ordinary q` hypotheses: declared base types are paid by actual base typing. Ranked declarations include only ground, including arity zero; no nonexistent curried ranked arrow is added. Auxiliary closure under literal subtypes and retention of every occurring head declaration are explicit targets.

This packet does not yet prove closure of recursive source requests, port normalization, finite observation enumeration, full tuple domain construction, fixed-point stabilization or adequacy. Those obligations remain pending. No compiler or proof implementation preceded this freeze.
