# Paper 17: effectivity of the indexed assignment's actual constructors

The gate proves joint partial recursiveness for the original indexed numeral, optional box tail, recursor, and application constructors. Typed argument packing does not replace the original recursor tuple or selected literal constructor. The optional tail preserves its two original continuations, and no divergence in an invoked policy operation is converted to a returned option. This gate does not check the complete assignment, abstraction, or ground compiler.
