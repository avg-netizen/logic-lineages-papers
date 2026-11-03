# Typed one-hole contexts for actual numbered reduction

The mutually inductive context data stores an actual hole context/type and an actual result context/type. It permits only lambda, function-side auxiliary application, ordinary base arguments, numbered base arguments and numbered extras, using argument head/tail contexts to identify exactly one occurrence. A lambda changes the surrounding binder context precisely in its type. Unchanged siblings are literal typed syntax. There is no positive application-argument context, no context constructor for a variable/bottom, and no empty argument context.

The executable mutual plug operations rebuild the actual syntax with the supplied typed hole term. Two targets lift an explicit genuine WindowStep at that hole to a WindowStep or WindowArgumentStep of the plugged syntax by actual mutual context induction. The leaf premise remains visible and is an induction interface to be discharged by a later recursive checker. No Good or SubtypeClosed premise is needed for pure context closure; preservation of universe remains a separate existing theorem when its assumptions hold.

This is not completeness of a recursive certificate parser, a full rule decision, an arithmetic representation, or an accessibility result. It neither adds unsupported positive contexts nor alters the original comparison or its transitivity obstruction.
