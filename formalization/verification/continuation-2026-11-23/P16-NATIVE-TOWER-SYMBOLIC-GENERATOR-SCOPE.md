# Paper 16: symbolic exact tower generator fold

The symbolic bridge checks the actual code-level lowering and outer
application equations without specializing the numeric fixed constants.
Its result uses the already checked literal native type and application
codec bridges. The specialization to the three original closed native
constants and exact equality to `towerCode` remains separate: the first
specialization root stopped at the resident-memory limit. This record
is neither that specialization nor ordinal semantics.
