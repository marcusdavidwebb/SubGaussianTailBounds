## Change

Describe the scope, affected declarations/constants and attribution. Follow
[CONTRIBUTING.md](../CONTRIBUTING.md), including the contribution-history entry.
Identify any verification-policy change requiring separate review.

## Verification

Record the candidate and accepted-base commit IDs, exact command and actual
result of the complete [local verification](../docs/VERIFICATION.md), plus other
checks performed. State failed, skipped or interrupted checks explicitly.
The immutable root statement must remain byte-for-byte unchanged.

Marcus Webb repeats the complete accepted-base check before merging every PR.
Green administrative CI is not Lean proof verification.
