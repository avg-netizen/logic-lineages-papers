"""Pure-R1 arithmetic below epsilon_0 and finite respecting-pattern syntax.

Semantic identification with recursive Sigma1-elementarity is a published
external theorem, not a claim that finite tests prove that identification.
"""
from .ordinals import (CNF, ZERO, ONE, OMEGA, nat, power, normal, add, mul_nat,
                       principal_sum, last_exponent, endpoint, resembles,
                       compare, unary_tree_size, pretty, lean_term)
from .parser import InputLimitError, parse_ordinal
from .patterns import (Pattern, SearchLimitError, is_morphism, morphisms,
                       covers, embeds, pure_r1_trace, enumerate_patterns)
from .jsonio import cnf_to_data, cnf_from_data, pattern_to_data, pattern_from_data

__version__ = "0.1.0"
__all__ = [
    "CNF", "ZERO", "ONE", "OMEGA", "nat", "power", "normal", "add", "mul_nat",
    "principal_sum", "last_exponent", "endpoint", "resembles", "compare",
    "unary_tree_size", "pretty", "lean_term", "InputLimitError", "parse_ordinal",
    "Pattern", "SearchLimitError", "is_morphism", "morphisms", "covers", "embeds",
    "pure_r1_trace", "enumerate_patterns", "cnf_to_data", "cnf_from_data",
    "pattern_to_data", "pattern_from_data",
]
