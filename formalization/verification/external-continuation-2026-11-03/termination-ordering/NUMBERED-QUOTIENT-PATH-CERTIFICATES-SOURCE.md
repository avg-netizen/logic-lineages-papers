# Exact finite quotient-path certificates

Each ordered list entry contains the next vertex and an actual numeric QuotientEdge certificate from the current vertex. The recursive checker validates every edge using the accepted concrete edge checker and requires the last vertex equal the requested target. Empty lists represent exactly zero edges and endpoint equality, matching CountedPath.refl on arbitrary naturals; no unproved carrier assumption is silently added. Positive certificates require a nonempty list.

Three targets give exact list-length/count correspondence to the existing CountedPath, exact nonempty-list correspondence to the existing PositivePath, and an all-natural positive certificate wrapper using the accepted ordered natural-list codec and literal pair inverses. Concatenation must preserve all edges/counts; intermediate witnesses are the actual listed vertices. The only underlying relation is the accepted QuotientEdge at explicit signature/context/window/Boolean-table parameters.

This checks a supplied finite path and proves existential certificate completeness. It does not implement unbounded search/enumeration, decide absence of a path, establish formal arithmetic representability or prove well-foundedness/accessibility. No original ordering or reduction rule is changed.
