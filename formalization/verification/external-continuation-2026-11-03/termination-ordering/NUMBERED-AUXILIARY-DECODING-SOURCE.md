# Actual typed decoding and finite candidate coverage

This is a prerequisite for paper06's finite computable primary classes, not a completed quotient or equivalence decision procedure.

The decoder checks the literal structural code against an actual context and requested result type (or exact ordered argument-type list). Variable indices are checked against actual typed context entries. Binder annotations, application domains, native/ranked head identities, ordered base arguments, numbered result annotations, complete extra-type lists and all extra arguments are preserved. A malformed or mismatched code returns none. No replacement term, default type, typing oracle or equivalence test is used.

The six targets give actual term and argument round trips, exact code recovery on successful term and argument decoding, packed round trip, and finite typed candidate coverage of every restricted primary equivalent term. Candidates are obtained by filterMap of the previously proved covering code list. They may include terms outside the primary class and are not asserted to form the exact class. Enumeration bounds and universe preservation remain the prior proved suppliers. All decoder and candidate definitions are ordinary executable definitions.
