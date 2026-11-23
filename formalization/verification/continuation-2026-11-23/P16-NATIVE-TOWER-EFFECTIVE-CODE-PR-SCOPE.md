# Paper 16: primitive-recursive numeric tower generator

The checked module proves primitive recursion for the exact shared
`generate` program, both jointly in its three explicit numeric constants
and its index and with the constants fixed. It also checks the descending
code fold and homogeneous application step. The separate equality from
this same function with the original fixed native constants to the
original `towerCode` is not asserted here; its attempted mixed proof
stopped at the resident-memory limit. Acceptance #1475 independently
establishes the exact original term code and positive typed decode, not
primitive recursiveness of that literal code by itself.

This record therefore does not yet certify the connection between the
two independently checked properties. It makes no ordinal claim and no
numbered promotion.
