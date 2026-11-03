# Actual typed-variable decoder success primitive recursion

Paper06 lines551–556 requires effective coded typed syntax. This component addresses exactly the variable branch of the accepted dependent decoder. Its success bit equals literal typed-context lookup at the actual de Bruijn index, including empty contexts, out-of-range indices and wrong types. That exact Boolean function is proved formally Primrec uniformly in the entire context, expected type and index, using the already established literal Ty presentation.

No Primcodable instance for a dependent Variable family is assumed. No changes to decodeVariable, no invented bound/default, and no claim about mutual decodeTerm/decodeArguments, packed syntax, the full checker or arithmetic representability.
