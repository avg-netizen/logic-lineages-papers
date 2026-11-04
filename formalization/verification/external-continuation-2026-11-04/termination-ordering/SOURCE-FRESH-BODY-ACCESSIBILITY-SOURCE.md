# Fresh-variable identity and explicitly conditional body accessibility

Draft for review; no proof/export. Paper 06 lines 590–597 says choosing u=x yields accessibility of the body. The context distinction is explicit here.

freshInstance body renames the original body from sigma::Gamma into sigma::sigma::Gamma by lifting weakening Gamma→sigma::Gamma, then substitutes the fresh variable here in sigma::Gamma for the lambda binder. The identity theorem says the resulting term literally equals body, at the identical type and context. Existing bindingRetraction applies: on here and there variables the composed map is the corresponding variable. This is not arbitrary term weakening stability.

The second target assumes actual C_tau of this fresh instance IN sigma::Gamma, successful decode, subtype closure, and scalar calibration for encodedScalar/encodedR IN sigma::Gamma. It concludes literal reverse body-R Acc there, via the identity, accepted C⇒Acc and matching relation calibration. No premise in Gamma is silently moved to sigma::Gamma. Typedness/confinement follow from the supplied computability if needed; no absent fresh-variable condition in Gamma is assumed.

This does not derive fresh-context computability from the previous same-context universal beta premise. Context transport, fundamental computable substitution and all-term termination remain open. No ID1 or publication claim.
