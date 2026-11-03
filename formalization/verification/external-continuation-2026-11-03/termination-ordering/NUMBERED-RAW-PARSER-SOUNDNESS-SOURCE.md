# Actual raw numeric parser successful-parse soundness

Paper06 lines551–556 requires exact coded syntax for the quotient relations. This component establishes a literal invariant of the accepted numeric parsers before their outer validation filters: whenever an actual type, type-list, head or recursive code parser succeeds, re-encoding its returned value gives exactly the original natural input.

Fuel is arbitrary, including zero; no successful parsing is assumed where the actual parser fails. All head and recursive syntax tags and malformed-payload restrictions are retained. Recursive code children use strictly smaller fuel. Existing validated type/list/head subdecoders remain the actual dependencies. No parser definition is changed and no validation filter is removed.

The results do not claim formal primitive recursion of recursive code parsing, totality or typing validity of arbitrary Code, full checker effectivity, arithmetic representability, accessibility or well-foundedness.
